// --------------------------------------------------------------------------
// Licensed Materials - Property of IBM
//
// 5725-A06 5725-A29 5724-Y48 5724-Y49 5724-Y54 5724-Y55
// Copyright IBM Corporation 1998, 2022. All Rights Reserved.
//
// Note to U.S. Government Users Restricted Rights:
// Use, duplication or disclosure restricted by GSA ADP Schedule
// Contract with IBM Corp.
// --------------------------------------------------------------------------

// Problem 3 from Model Building in Mathematical Programming, 3rd ed.
//   by HP Williams
// Factory Planning　1
// 工場計画I
// https://www.ibm.com/docs/ja/icos/20.1.0?topic=library-manufacturing#usroplsamples.uss_opl_modlib.1019740__usroplsamples.uss_opl_modlib.1019805
// This model is described in the documentation. 
// See IDE and OPL > Language and Interfaces Examples.

//// データ
// 製品名
{string} Prod = ...;
// プロセス名
{string} Process = ...;

// 計画を立てる月数
int NbMonths = ...;
range Months = 1..NbMonths;
//初期在庫＋月。在庫の制約を最初の月とそれ以降で分けないため
range R0 = 0..NbMonths;

// 製品種ごとの利益
float ProfitProd[Prod] = ...;
// 製品種ごとの必要プロセス時間[プロセス,月]
float ProcessProd[Process][Prod] = ...;
// 各月の製品種毎の最大需要数[月,製品]
int MarketProd[Months][Prod] = ...;

// ひと月の稼働時間/台
float HoursMonth = ...;
// 各プロセスの毎月の稼働可能台数[プロセス,月]
float NumProcess[Process][Months] = ...;

// １製品の在庫コスト/月
float CostHold = ...;
// 初期在庫数
float StartHold = ...;
// 最終在庫数
float EndHold = ...;
// 最大在庫可能数
int MaxHold = ...;



//// 決定変数
// 製造数[製品,月]
//dvar float+ Make[Prod][Months];
dvar int+ Make[Prod][Months];
// 在庫数[製品,初期在庫+月]。制約1:在庫数が最大在庫可能数以下
//dvar float+ Hold[Prod][R0] in 0..MaxHold;
dvar int+ Hold[Prod][R0] in 0..MaxHold;
// 販売数[製品,月]。制約2:販売数が最大需要数以下
//dvar float+ Sell[j in Prod][m in Months] in 0..MarketProd[m,j];
dvar int+ Sell[j in Prod][m in Months] in 0..MarketProd[m,j];

//// 決定関数
// 売上＝製品ごとの売上*販売数
dexpr float Sales = 
  sum (j in Prod, m in Months) ProfitProd[j] * Sell[j][m];
// コスト＝在庫コスト*在庫量
dexpr float Cost = 
  sum (j in Prod, m in Months) CostHold * Hold[j][m];
// 粗利=売上-コスト
dexpr float GrossProfit = Sales - Cost;

  
//// 目的関数
// 粗利の最大化
maximize GrossProfit;
        
//// 制約
subject to {
  // Limits on process capacity
  // 制約3:毎月の各プロセスの製造可能数以下
  forall(m in Months, i in Process)
    ct1Capacity: sum(j in Prod) ProcessProd[i][j] * Make[j][m]
           <= NumProcess[i][m] * HoursMonth;

  // Inventory balance
  // 制約4:前月在庫数＋製造数と販売数＋当月在庫が等しい
  forall(j in Prod, m in Months)
    ct2InvBal: Hold[j][m-1] + Make[j][m] == Sell[j][m] + Hold[j][m];

  // Starting and ending inventories are fixed
  // 制約5:初期在庫数と最終在庫数は固定値
  forall(j in Prod) {
    ct3StartInv: Hold[j][0] == StartHold;    
    ct4EndInv: Hold[j][NbMonths] == EndHold;
  }
}


// 結果の表示
execute DISPLAY {
   //plan[m][j] describes how much to make, sell, and hold of each product j in each month m
   // plan[m][j] は、各製品 j を毎月 m にどれだけ製造、販売、保有するかを記述します。
   for(var m in Months)
      for(var j in Prod)
         writeln("plan[",m,"][",j,"] = <Make:",Make[j][m],", Sell:",Sell[j][m],", Hold:",Hold[j][m],">");
}
