// ============================================================
// UN-R13H 5.2.23 ESS — フルヒステリシス対応版 (1152状態空間)
// (減速度・予測・ABS すべてにヒステリシスを実装)
// ============================================================

enum Decel         { DLow, DMid, DHigh } // 実減速度: <2.5, 2.5-6.0, >=6.0
enum Demand        { QLow, QMid, QHigh } // 制動要求(予測): <2.5, 2.5-6.0, >=6.0 (QMid追加)
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
// Forbidden 述語群
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

// isForbidden (すべての禁止ルールを集約)
pred isForbidden [dd:Decel, qq:Demand, ss:Spd, bb:Brk, aa:Abs, dp:DesignPattern, pg:Sig, gg:Sig] {
    forbidden_5_2_23[bb, gg]
    or forbidden_5_2_23_1[dd, pg, gg]
    or forbidden_5_2_23_2a[qq, dp, pg, gg]
    or forbidden_5_2_23_2b[ss, aa, dp, pg, gg] // pgを追加
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