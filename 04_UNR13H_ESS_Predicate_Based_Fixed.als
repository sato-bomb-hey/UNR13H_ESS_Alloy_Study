// ============================================================
// UN-R13H 5.2.23 ESS – 述語直接検証・仕様ギャップ修正版
// ============================================================
// 変更点:
//   check noGap が以下の反例を返した（仕様ギャップ）:
//     decel=DHigh, demand=QHigh, brake=BOn, signal=Deact
//   この状態は isForbidden=false（消灯禁止ルールはない）かつ
//   isPermitted=false（Deact を明示許可するルールがなかった）で
//   Unspecified になっていた。
//
//   根本原因:
//     UN-R13H 5.2.23 の活性化条件は "may"（許可）であり "shall"（義務）
//     ではない。ブレーキ作動中の消灯を禁止するルールは存在しないが、
//     isPermitted がブレーキ作動中の Deact 状態を網羅していなかった。
//
//   修正:
//     permitted_deact_while_braking を追加し、ブレーキ作動中の
//     消灯を常に Permitted とする。これにより check noGap が通る。
// ============================================================

enum Decel         { DLow, DMid, DHigh }           // 実減速度: <2.5, 2.5-6.0, >=6.0 m/s2
enum Demand        { QLow, QMid, QHigh }            // 制動要求（予測値）: 同区分
enum Spd           { SLow, SHigh }                  // 速度: <=50, >50 km/h
enum Brk           { BOn, BOff }                    // ブレーキ作動状態
enum Abs           { AFull, ANot }                  // ABS状態
enum DesignPattern { MeasOnly, MeasPred, MeasAbsM, MeasPredAbsM }
enum Sig           { Act, Deact }                   // 信号状態

// ===== ヘルパー述語 =====

pred usesPred [dp: DesignPattern] { dp = MeasPred or dp = MeasPredAbsM }
pred usesAbsM [dp: DesignPattern] { dp = MeasAbsM or dp = MeasPredAbsM }

// ============================================================
// 点灯トリガー群 – 各トリガーが独立した前回状態を参照
// ============================================================

// 1. 実減速度トリガー
//    新規点灯: DHigh (>=6.0) に到達した場合のみ
//    維持    : DMid (2.5-6.0) かつ prevMeas=Act（自身が前回発火）
pred trigger_meas [dd: Decel, pm: Sig] {
    dd = DHigh
    or (dd = DMid and pm = Act)
}

// 2. 予測トリガー
//    新規点灯: QHigh (>=6.0) に到達した場合のみ
//    維持    : QMid (2.5-6.0) かつ prevPred=Act（自身が前回発火）
pred trigger_pred [qq: Demand, dp: DesignPattern, pp: Sig] {
    usesPred[dp] and (
        qq = QHigh
        or (qq = QMid and pp = Act)
    )
}

// 3. ABSトリガー
//    新規点灯: SHigh (>50km/h) かつ ABS作動
//    維持    : ABS作動中 かつ prevAbs=Act（自身が前回発火）
pred trigger_abs [ss: Spd, aa: Abs, dp: DesignPattern, pa: Sig] {
    usesAbsM[dp] and aa = AFull and (
        ss = SHigh
        or pa = Act
    )
}

// 統合トリガー: いずれか1つでも発火すれば点灯許可
pred anyTriggerFires [dd: Decel, qq: Demand, ss: Spd, aa: Abs,
                      dp: DesignPattern, pm: Sig, pp: Sig, pa: Sig] {
    trigger_meas[dd, pm]
    or trigger_pred[qq, dp, pp]
    or trigger_abs[ss, aa, dp, pa]
}

// ============================================================
// Forbidden 述語群
// ============================================================

// 5.2.23: ブレーキ非作動時の点灯は絶対禁止
pred forbidden_5_2_23 [bb: Brk, cg: Sig] {
    cg = Act and bb = BOff
}

// 5.2.23.1: 実減速度の禁止ルール（prevMeas を参照）
//   - DLow (<2.5): 無条件禁止
//   - DMid (2.5-6.0) かつ prevMeas=Deact: 新規点灯禁止
//     （実減速度トリガーが一度も DHigh に達していないので維持不可）
pred forbidden_5_2_23_1 [dd: Decel, pm: Sig, cg: Sig] {
    (cg = Act and dd = DLow)
    or
    (cg = Act and dd = DMid and pm = Deact)
}

// 5.2.23.2a: 予測値の禁止ルール（prevPred を参照）
//   - QLow (<2.5): 無条件禁止
//   - QMid (2.5-6.0) かつ prevPred=Deact: 新規点灯禁止
pred forbidden_5_2_23_2a [qq: Demand, dp: DesignPattern, pp: Sig, cg: Sig] {
    usesPred[dp] and (
        (cg = Act and qq = QLow)
        or
        (cg = Act and qq = QMid and pp = Deact)
    )
}

// 5.2.23.2b: ABSの禁止ルール（prevAbs を参照）
//   - ANot (ABS非作動): 無条件禁止
//   - AFull かつ SLow かつ prevAbs=Deact: 新規点灯禁止
//     （ABSトリガーが一度も SHigh で発火していないので維持不可）
pred forbidden_5_2_23_2b [ss: Spd, aa: Abs, dp: DesignPattern, pa: Sig, cg: Sig] {
    usesAbsM[dp] and (
        (cg = Act and aa = ANot)
        or
        (cg = Act and ss = SLow and pa = Deact)
    )
}

// 統合 Forbidden:
//   - ブレーキ非作動は絶対禁止（トリガーで救えない）
//   - 個別禁止条件に引っかかる かつ anyTriggerFires が救わない場合
pred isForbidden [dd: Decel, qq: Demand, ss: Spd, bb: Brk, aa: Abs,
                  dp: DesignPattern, pm: Sig, pp: Sig, pa: Sig, cg: Sig] {
    forbidden_5_2_23[bb, cg]
    or
    (bb = BOn
     and (forbidden_5_2_23_1[dd, pm, cg]
          or forbidden_5_2_23_2a[qq, dp, pp, cg]
          or forbidden_5_2_23_2b[ss, aa, dp, pa, cg])
     and not anyTriggerFires[dd, qq, ss, aa, dp, pm, pp, pa])
}

// ============================================================
// Permitted 述語群
// ============================================================

// --- 実減速度 (Meas) ---

// DHigh で点灯許容
pred permitted_5_2_23_1_may [dd: Decel, bb: Brk, cg: Sig] {
    cg = Act and dd = DHigh and bb = BOn
}
// DHigh でも消灯は許容（点灯は may であり shall ではない）
pred permitted_5_2_23_1_deact [dd: Decel, bb: Brk, cg: Sig] {
    cg = Deact and dd = DHigh and bb = BOn
}
// DLow で消灯許容
pred permitted_5_2_23_1_shall_deact [dd: Decel, bb: Brk, cg: Sig] {
    cg = Deact and dd = DLow and bb = BOn
}
// 実減速度ヒステリシス: prevMeas=Act なら DMid で点灯維持可
pred permitted_hysteresis [dd: Decel, bb: Brk, pm: Sig, cg: Sig] {
    dd = DMid and bb = BOn and pm = Act and cg = Act
}
// DMid でブレーキ中の消灯は prevMeas に関わらず常に許容
// （ヒステリシスは維持を許可するが消灯を禁止しない。点灯は may）
pred permitted_hysteresis_deact [dd: Decel, bb: Brk, cg: Sig] {
    dd = DMid and bb = BOn and cg = Deact
}

// --- 予測 (Pred) ---

// QHigh で点灯許容
pred permitted_5_2_23_2a_may [qq: Demand, bb: Brk, dp: DesignPattern, cg: Sig] {
    usesPred[dp] and cg = Act and qq = QHigh and bb = BOn
}
// QLow で消灯許容
pred permitted_5_2_23_2a_shall_deact [qq: Demand, bb: Brk, dp: DesignPattern, cg: Sig] {
    usesPred[dp] and cg = Deact and qq = QLow and bb = BOn
}
// 予測ヒステリシス: prevPred=Act なら QMid で点灯維持可
pred permitted_pred_hysteresis [qq: Demand, bb: Brk, dp: DesignPattern, pp: Sig, cg: Sig] {
    usesPred[dp] and qq = QMid and bb = BOn and pp = Act and cg = Act
}

// --- ABS ---

// SHigh + AFull で点灯許容（新規点灯条件）
pred permitted_5_2_23_2b_may [ss: Spd, aa: Abs, bb: Brk, dp: DesignPattern, cg: Sig] {
    usesAbsM[dp] and cg = Act and ss = SHigh and aa = AFull and bb = BOn
}
// ANot で消灯許容
pred permitted_5_2_23_2b_shall_deact [aa: Abs, dp: DesignPattern, cg: Sig] {
    usesAbsM[dp] and cg = Deact and aa = ANot
}
// ABS 作動中でも消灯は許容（点灯は may であり shall ではない）
pred permitted_5_2_23_2b_deact [aa: Abs, bb: Brk, dp: DesignPattern, cg: Sig] {
    usesAbsM[dp] and cg = Deact and aa = AFull and bb = BOn
}
// ABSヒステリシス: prevAbs=Act なら AFull+SLow でも点灯維持可
pred permitted_abs_hysteresis [aa: Abs, bb: Brk, dp: DesignPattern, pa: Sig, cg: Sig] {
    usesAbsM[dp] and aa = AFull and bb = BOn and pa = Act and cg = Act
}

// --- その他 ---

// ブレーキ非作動時は消灯許容
pred permitted_brake_off [bb: Brk, cg: Sig] {
    bb = BOff and cg = Deact
}

// 統合 Permitted
pred isPermitted [dd: Decel, qq: Demand, ss: Spd, bb: Brk, aa: Abs,
                  dp: DesignPattern, pm: Sig, pp: Sig, pa: Sig, cg: Sig] {
    permitted_5_2_23_1_may[dd, bb, cg]
    or permitted_5_2_23_1_deact[dd, bb, cg]
    or permitted_5_2_23_1_shall_deact[dd, bb, cg]
    or permitted_hysteresis[dd, bb, pm, cg]
    or permitted_hysteresis_deact[dd, bb, cg]
    or permitted_5_2_23_2a_may[qq, bb, dp, cg]
    or permitted_5_2_23_2a_shall_deact[qq, bb, dp, cg]
    or permitted_pred_hysteresis[qq, bb, dp, pp, cg]
    or permitted_5_2_23_2b_may[ss, aa, bb, dp, cg]
    or permitted_5_2_23_2b_shall_deact[aa, dp, cg]
    or permitted_5_2_23_2b_deact[aa, bb, dp, cg]
    or permitted_abs_hysteresis[aa, bb, dp, pa, cg]
    or permitted_brake_off[bb, cg]
}

// ============================================================
// 検証コマンド群 (Cell なし・全称量化で直接駆動)
// ============================================================
// 変数の意味:
//   d=decel  q=demand  s=speed  b=brake  a=abs
//   dp=designPattern  pm=prevMeas  pp=prevPred  pa=prevAbs  cg=signal

// [検証1] 矛盾なし: Forbidden かつ Permitted になる状態は存在しない
check noConflict {
    all d: Decel, q: Demand, s: Spd, b: Brk, a: Abs, dp: DesignPattern,
        pm: Sig, pp: Sig, pa: Sig, cg: Sig |
        not (isForbidden[d,q,s,b,a,dp,pm,pp,pa,cg]
             and isPermitted[d,q,s,b,a,dp,pm,pp,pa,cg])
}

// [検証2] 網羅性: Unspecified（どちらでもない）な状態は存在しない
check noGap {
    all d: Decel, q: Demand, s: Spd, b: Brk, a: Abs, dp: DesignPattern,
        pm: Sig, pp: Sig, pa: Sig, cg: Sig |
        isForbidden[d,q,s,b,a,dp,pm,pp,pa,cg]
        or isPermitted[d,q,s,b,a,dp,pm,pp,pa,cg]
}

// [例示] Forbidden な状態を一つ表示する
run showForbidden {
    some d: Decel, q: Demand, s: Spd, b: Brk, a: Abs, dp: DesignPattern,
        pm: Sig, pp: Sig, pa: Sig, cg: Sig |
        isForbidden[d,q,s,b,a,dp,pm,pp,pa,cg]
        and not isPermitted[d,q,s,b,a,dp,pm,pp,pa,cg]
}

// [例示] Permitted な状態を一つ表示する
run showPermitted {
    some d: Decel, q: Demand, s: Spd, b: Brk, a: Abs, dp: DesignPattern,
        pm: Sig, pp: Sig, pa: Sig, cg: Sig |
        isPermitted[d,q,s,b,a,dp,pm,pp,pa,cg]
        and not isForbidden[d,q,s,b,a,dp,pm,pp,pa,cg]
}
