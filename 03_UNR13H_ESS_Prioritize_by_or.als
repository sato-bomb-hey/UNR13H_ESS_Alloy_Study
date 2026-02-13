// ============================================================
// UN-R13H 5.2.23 ESS ? フルヒステリシス・OR回路化版 (1152状態空間)
// ============================================================
// 5.2.23.1 / 5.2.23.2(a) / 5.2.23.2(b) の作動許可条件を OR 結合し、
// さらに 予測(Demand) と ABS にもヒステリシス論理を適用したバージョン。

enum Decel         { DLow, DMid, DHigh } // 実減速度: <2.5, 2.5-6.0, >=6.0
enum Demand        { QLow, QMid, QHigh } // 【追加】制動要求: <2.5, 2.5-6.0, >=6.0
enum Spd           { SLow, SHigh }       // 速度: <=50, >50
enum Brk           { BOn, BOff }         // ブレーキ作動状態
enum Abs           { AFull, ANot }       // ABS状態
enum DesignPattern { MeasOnly, MeasPred, MeasAbsM, MeasPredAbsM }
enum Sig           { Act, Deact }        // 信号出力状態 (Current & Previous)
enum Status        { Forbidden, Permitted, Conflict, Unspecified }

// ===== 状態空間セル (1152通り) =====


sig Cell {
    decel       : one Decel,
    demand      : one Demand,
    speed       : one Spd,
    brake       : one Brk,
    abs         : one Abs,
    design      : one DesignPattern,
    prevSignal  : one Sig,
    signal      : one Sig,
    status      : one Status
} {
    // 全組み合わせの網羅制約
    all c: Cell - this | 
        decel != c.@decel or demand != c.@demand or 
        speed != c.@speed or brake != c.@brake or 
        abs != c.@abs or design != c.@design or 
        prevSignal != c.@prevSignal or signal != c.@signal
}

// ===== ヘルパー述語 =====

pred usesPred [dp: DesignPattern] { dp = MeasPred or dp = MeasPredAbsM }
pred usesAbsM [dp: DesignPattern] { dp = MeasAbsM or dp = MeasPredAbsM }

// ============================================================
// 点灯トリガー (OR回路の構成要素) - ヒステリシス対応
// ============================================================

// 1. 実減速度トリガー (6.0以上 or 2.5以上かつ維持)
pred trigger_meas [dd:Decel, pg:Sig] {
    dd = DHigh
    or (dd = DMid and pg = Act)
}

// 2. 予測トリガー (6.0以上 or 2.5以上かつ維持) 
pred trigger_pred [qq:Demand, dp:DesignPattern, pg:Sig] {
    usesPred[dp] and (
        qq = QHigh
        or (qq = QMid and pg = Act) // QMidでの維持を追加
    )
}

// 3. ABSトリガー (50km/h以上 or 速度不問かつ維持) 
pred trigger_abs [ss:Spd, aa:Abs, dp:DesignPattern, pg:Sig] {
    usesAbsM[dp] and aa = AFull and (
        ss = SHigh
        or pg = Act // 前回点灯していれば速度不問で維持
    )
}

// 統合トリガー: どれか一つでもONなら点灯許可
pred anyTriggerFires [dd:Decel, qq:Demand, ss:Spd, aa:Abs, dp:DesignPattern, pg:Sig] {
    trigger_meas[dd, pg]
    or trigger_pred[qq, dp, pg] // pgを追加
    or trigger_abs[ss, aa, dp, pg] // pgを追加
}

// ============================================================
// Forbidden 述語群 (?してはならない)
// ============================================================

// 5.2.23: ブレーキ作動時のみ
pred forbidden_5_2_23 [bb:Brk, gg:Sig] {
    gg = Act and bb = BOff
}

// 5.2.23.1: 実減速度の禁止ルール
pred forbidden_5_2_23_1 [dd:Decel, pg:Sig, gg:Sig] {
    // 1. 減速度 < 2.5 (DLow) なら、無条件で点灯禁止
    (gg = Act and dd = DLow)
    or
    // 2. 減速度 < 6.0 (DMid) かつ 前回消灯 (Deact) なら、"新規の"点灯禁止
    (gg = Act and dd = DMid and pg = Deact)
}

// 5.2.23.2a: 予測値の禁止ルール (ヒステリシス対応)
pred forbidden_5_2_23_2a [qq:Demand, dp:DesignPattern, pg:Sig, gg:Sig] {
    usesPred[dp] and (
        // 1. 予測値 < 2.5 (QLow) なら、無条件で点灯禁止
        (gg = Act and qq = QLow)
        or
        // 2. 予測値 < 6.0 (QMid) かつ 前回消灯 (Deact) なら、"新規の"点灯禁止
        (gg = Act and qq = QMid and pg = Deact)
    )
}

// 5.2.23.2b: ABSの禁止ルール (ヒステリシス対応)
// 【修正】ABS作動中(AFull)で前回点灯(Act)なら、速度が低くても(SLow)禁止しない
pred forbidden_5_2_23_2b [ss:Spd, aa:Abs, dp:DesignPattern, pg:Sig, gg:Sig] {
    usesAbsM[dp] and (
        // 1. ABS非作動 (ANot) なら、無条件で点灯禁止
        (gg = Act and aa = ANot)
        or
        // 2. 速度 <= 50 (SLow) かつ 前回消灯 (Deact) なら、"新規の"点灯禁止
        //    (逆に言えば、前回点灯していれば低速でも維持してよい)
        (gg = Act and ss = SLow and pg = Deact)
    )
}

// 統合Forbidden: OR回路(anyTriggerFires)が効いていない時のみ禁止
pred isForbidden [dd:Decel, qq:Demand, ss:Spd, bb:Brk, aa:Abs, dp:DesignPattern, pg:Sig, gg:Sig] {
    // (1) ブレーキ非作動は絶対禁止
    forbidden_5_2_23[bb, gg]
    or
    // (2) 個別禁止かつ、どのトリガーも救ってくれない場合
    (bb = BOn
     and (forbidden_5_2_23_1[dd, pg, gg]
          or forbidden_5_2_23_2a[qq, dp, pg, gg] // pgを追加
          or forbidden_5_2_23_2b[ss, aa, dp, pg, gg]) // pgを追加
     and not anyTriggerFires[dd, qq, ss, aa, dp, pg])
}

// ============================================================
// Permitted 述語群
// ============================================================

// --- 実減速度 (Meas) ---
// 減速度 >= 6.0 で点灯許容
pred permitted_5_2_23_1_may [dd:Decel, bb:Brk, gg:Sig] {
    gg = Act and dd = DHigh and bb = BOn
}
// 減速度 < 2.5 で消灯許容
pred permitted_5_2_23_1_shall_deact [dd:Decel, bb:Brk, gg:Sig] {
    gg = Deact and dd = DLow and bb = BOn
}
// 減速度ヒステリシス (DMid で維持)
pred permitted_hysteresis [dd:Decel, bb:Brk, pg:Sig, gg:Sig] {
    dd = DMid and bb = BOn and gg = pg
}

// --- 予測 (Pred) ---

// 予測 >= 6.0 で点灯許容
pred permitted_5_2_23_2a_may [qq:Demand, bb:Brk, dp:DesignPattern, gg:Sig] {
    usesPred[dp] and gg = Act and qq = QHigh and bb = BOn
}
// 予測 < 2.5 で消灯許容
pred permitted_5_2_23_2a_shall_deact [qq:Demand, bb:Brk, dp:DesignPattern, gg:Sig] {
    usesPred[dp] and gg = Deact and qq = QLow and bb = BOn
}
// 予測ヒステリシス (QMid で維持)
pred permitted_pred_hysteresis [qq:Demand, bb:Brk, dp:DesignPattern, pg:Sig, gg:Sig] {
    usesPred[dp] and qq = QMid and bb = BOn and gg = pg
}

// --- ABS ---

// ABS開始条件: 速度 > 50 かつ ABS作動
pred permitted_5_2_23_2b_may [ss:Spd, aa:Abs, bb:Brk, dp:DesignPattern, gg:Sig] {
    usesAbsM[dp] and gg = Act and ss = SHigh and aa = AFull and bb = BOn
}
// ABS停止条件: ABS非作動 (速度不問)
pred permitted_5_2_23_2b_shall_deact [aa:Abs, dp:DesignPattern, gg:Sig] {
    usesAbsM[dp] and gg = Deact and aa = ANot
}
// ABS作動中なら速度不問で維持
pred permitted_abs_hysteresis [aa:Abs, bb:Brk, dp:DesignPattern, pg:Sig, gg:Sig] {
    usesAbsM[dp] and aa = AFull and bb = BOn and gg = Act and pg = Act
    // ※速度(ss)条件を含めないことで、SLowでも維持可能にする
}

// --- その他 ---
// ブレーキ非作動時は消灯
pred permitted_brake_off [bb:Brk, gg:Sig] {
    bb = BOff and gg = Deact
}

// isPermitted (すべての許可ルールを集約)
pred isPermitted [dd:Decel, qq:Demand, ss:Spd, bb:Brk, aa:Abs, dp:DesignPattern, pg:Sig, gg:Sig] {
    permitted_5_2_23_1_may[dd, bb, gg]
    or permitted_5_2_23_1_shall_deact[dd, bb, gg]
    or permitted_hysteresis[dd, bb, pg, gg]
    or permitted_5_2_23_2a_may[qq, bb, dp, gg]
    or permitted_5_2_23_2a_shall_deact[qq, bb, dp, gg]
    or permitted_pred_hysteresis[qq, bb, dp, pg, gg]
    or permitted_5_2_23_2b_may[ss, aa, bb, dp, gg]
    or permitted_5_2_23_2b_shall_deact[aa, dp, gg]
    or permitted_abs_hysteresis[aa, bb, dp, pg, gg]     // 追加
    or permitted_brake_off[bb, gg]
}

// ============================================================
// 分類ルール & 網羅設定
// ============================================================

fact classify {
    all c: Cell {
        let d = c.decel, q = c.demand, s = c.speed, b = c.brake, a = c.abs, dp = c.design, pg = c.prevSignal, g = c.signal |
        {
            // isForbiddenにもpgを渡す
            c.status = Forbidden   iff (isForbidden[d,q,s,b,a,dp,pg,g] and not isPermitted[d,q,s,b,a,dp,pg,g])
            c.status = Permitted   iff (isPermitted[d,q,s,b,a,dp,pg,g] and not isForbidden[d,q,s,b,a,dp,pg,g])
            c.status = Conflict    iff (isForbidden[d,q,s,b,a,dp,pg,g] and isPermitted[d,q,s,b,a,dp,pg,g])
            c.status = Unspecified iff (not isForbidden[d,q,s,b,a,dp,pg,g] and not isPermitted[d,q,s,b,a,dp,pg,g])
        }
    }
}

// 実行と検証
run classify_all {} for exactly 1152 Cell 

check gapsExist { no c: Cell | c.status = Unspecified } for exactly 1152 Cell
check conflictsExist { no c: Cell | c.status = Conflict } for exactly 1152 Cell