// ============================================================
// UN-R13H 5.2.23 ESS — 初期コード + Demand Mid追加版 (576状態空間)
// ============================================================

// ===== 意味次元 =====

enum Decel         { DLow, DMid, DHigh } // 実減速度: <2.5, 2.5-6.0, >=6.0
enum Demand        { QLow, QMid, QHigh } // 【追加】制動要求(予測): <2.5, 2.5-6.0, >=6.0 
enum Spd           { SLow, SHigh }       // 速度: <=50, >50
enum Brk           { BOn, BOff }         // ブレーキ作動状態
enum Abs           { AFull, ANot }       // ABS状態
enum DesignPattern { MeasOnly, MeasPred, MeasAbsM, MeasPredAbsM }
enum Sig           { Act, Deact }        // 信号出力状態
enum Status        { Forbidden, Permitted, Conflict, Unspecified }

// ===== 状態空間セル (384 -> 576通り) =====
// 3(Decel) * 3(Demand) * 2(Speed) * 2(Brake) * 2(Abs) * 4(Design) * 2(Signal) = 576

sig Cell {
    decel   : one Decel,
    demand  : one Demand,
    speed   : one Spd,
    brake   : one Brk,
    abs     : one Abs,
    design  : one DesignPattern,
    signal  : one Sig,
    status  : one Status
} {
    // 【ユニーク制約】
    // 自分自身(this)と、他のすべてのCell(c)を比較し、
    // 少なくとも1つのフィールドが異なっていなければならない（＝完全に同じCellは許さない）
    // これにより、全パターンの網羅性が保証される。
    all c: Cell - this | 
        decel != c.@decel or demand != c.@demand or 
        speed != c.@speed or brake != c.@brake or 
        abs != c.@abs or design != c.@design or 
        signal != c.@signal
}

// ===== ヘルパー述語 =====

pred usesPred [dp: DesignPattern] { dp = MeasPred or dp = MeasPredAbsM }
pred usesAbsM [dp: DesignPattern] { dp = MeasAbsM or dp = MeasPredAbsM }

// ============================================================
// Forbidden 述語群 (〜してはならない)
// ============================================================

// 5.2.23: ブレーキ作動時のみ
pred forbidden_5_2_23 [bb:Brk, gg:Sig] {
    gg = Act and bb = BOff
}

// 5.2.23.1: 実減速度 < 2.5 での点灯禁止 (Meas常時適用)
pred forbidden_5_2_23_1 [dd:Decel, gg:Sig] {
    gg = Act and dd = DLow
}

// 5.2.23.2a: Pred採用時、予測値 < 2.5 での点灯禁止
// 【修正】QMid (2.5-6.0) は禁止対象外とする (実減速度DMidと同様)
pred forbidden_5_2_23_2a [qq:Demand, dp:DesignPattern, gg:Sig] {
    usesPred[dp] and gg = Act and qq = QLow
}

// 5.2.23.2b: AbsM採用時、speed<=50 or ABS非フルでの点灯禁止
pred forbidden_5_2_23_2b [ss:Spd, aa:Abs, dp:DesignPattern, gg:Sig] {
    usesAbsM[dp] and gg = Act and (ss = SLow or aa = ANot)
}

pred isForbidden [dd:Decel, qq:Demand, ss:Spd, bb:Brk, aa:Abs, dp:DesignPattern, gg:Sig] {
    forbidden_5_2_23[bb, gg]
    or forbidden_5_2_23_1[dd, gg]
    or forbidden_5_2_23_2a[qq, dp, gg]
    or forbidden_5_2_23_2b[ss, aa, dp, gg]
}

// ============================================================
// Permitted 述語群 (〜してよい / 〜するものとする)
// ============================================================

// 5.2.23.1: 実減速度 >= 6.0 で点灯許容
pred permitted_5_2_23_1_may [dd:Decel, bb:Brk, gg:Sig] {
    gg = Act and dd = DHigh and bb = BOn
}

// 5.2.23.1: 実減速度 < 2.5 で消灯
pred permitted_5_2_23_1_shall_deact [dd:Decel, bb:Brk, gg:Sig] {
    gg = Deact and dd = DLow and bb = BOn
}

// 5.2.23.2a: Pred採用時、予測値 >= 6.0 で点灯許容
pred permitted_5_2_23_2a_may [qq:Demand, bb:Brk, dp:DesignPattern, gg:Sig] {
    usesPred[dp] and gg = Act and qq = QHigh and bb = BOn
}

// 5.2.23.2b: AbsM採用時、点灯許容 (速度 > 50 かつ ABSフル)
pred permitted_5_2_23_2b_may [ss:Spd, aa:Abs, bb:Brk, dp:DesignPattern, gg:Sig] {
    usesAbsM[dp] and gg = Act and ss = SHigh and aa = AFull and bb = BOn
}

// 5.2.23.2b: AbsM採用時、ABS非フルで消灯
pred permitted_5_2_23_2b_shall_deact [aa:Abs, dp:DesignPattern, gg:Sig] {
    usesAbsM[dp] and gg = Deact and aa = ANot
}

pred isPermitted [dd:Decel, qq:Demand, ss:Spd, bb:Brk, aa:Abs, dp:DesignPattern, gg:Sig] {
    permitted_5_2_23_1_may[dd, bb, gg]
    or permitted_5_2_23_1_shall_deact[dd, bb, gg]
    or permitted_5_2_23_2a_may[qq, bb, dp, gg]
    or permitted_5_2_23_2b_may[ss, aa, bb, dp, gg]
    or permitted_5_2_23_2b_shall_deact[aa, dp, gg]
}

// ============================================================
// 分類ルール & 網羅設定
// ============================================================

fact classify {
    all c: Cell {
        let d = c.decel, q = c.demand, s = c.speed, b = c.brake, a = c.abs, dp = c.design, g = c.signal | {
            c.status = Forbidden   iff (isForbidden[d,q,s,b,a,dp,g] and not isPermitted[d,q,s,b,a,dp,g])
            c.status = Permitted   iff (isPermitted[d,q,s,b,a,dp,g] and not isForbidden[d,q,s,b,a,dp,g])
            c.status = Conflict    iff (isForbidden[d,q,s,b,a,dp,g] and isPermitted[d,q,s,b,a,dp,g])
            c.status = Unspecified iff (not isForbidden[d,q,s,b,a,dp,g] and not isPermitted[d,q,s,b,a,dp,g])
        }
    }
}

// 実行と検証
run classify_all {} for exactly 576 Cell 

check gapsExist { no c: Cell | c.status = Unspecified } for exactly 576 Cell
check conflictsExist { no c: Cell | c.status = Conflict } for exactly 576 Cell