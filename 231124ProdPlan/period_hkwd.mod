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

/*  ----------------------------------------------------
 *   OPL Model for Production planning Example
 *
 *   This model is described in the documentation. 
 *   See IDE and OPL > Language and Interfaces Examples.
 各期の組立台数、販売台数、在庫数の決定
 *   --------------------------------------------------- */

{string} ComputerTypes = ...;
{string} ComponentTypes = ...;

tuple computersToBuild {
   {string} components;
   int      price;
   int      maxInventory;
}
computersToBuild Computers[ComputerTypes] = ...;

//期間数
int NbPeriods = ...;
range Periods = 1..NbPeriods;

//期ごとの最大の組立可能台数
int MaxBuildPerPeriod[Periods] = ...;
//コンピュータの種類と期ごとの最小最大の需要量
int MinDemand[ComputerTypes][Periods] = ...;
int MaxDemand[ComputerTypes][Periods] = ...;

//最大在庫可能数
//int MaxInventory = 15;

//全期分のコンピュータータイプ毎の組立台数の合計。前の問題の結果から入力する
float TotalBuild[ComputerTypes] = ...;



////決定変数
/*  ----------------------------------------------------
 *   Variables:
 *   build --   How many of each computer type to build
 *         in each period
 *   inStockAtEndOfPeriod --   How many of each computer 
 *   type to hold over in inventory at the end of each
 *         period
 *   --------------------------------------------------- */
//各期間に各タイプのコンピューターを何台構築するか
//dvar float+ Build[ComputerTypes][Periods];
dvar int+ Build[ComputerTypes][Periods];
//各期間に各タイプのコンピューターを何台販売するか
//dvar float+ Sell[ComputerTypes][Periods];
dvar int+ Sell[ComputerTypes][Periods];
//各期間の終了時に在庫に保持する各コンピューター タイプの数
//dvar float+ InStockAtEndOfPeriod[ComputerTypes][Periods];
dvar int+ InStockAtEndOfPeriod[ComputerTypes][Periods];

////目的関数はない。各期に振り分けられる実行可能解を探す。

////制約
subject to {
  //制約0:最大在庫可能数より各期の在庫数が小さい
  //制約3でカバーされるためコメントアウト
  //forall(p in Periods)  
  //  ctInventoryCapacity:  
  //    sum(c in ComputerTypes) InStockAtEndOfPeriod[c][p] <= MaxInventory;

  //制約1:各期のコンピュータータイプごとの販売台数が最大需要数以下
  forall(c in ComputerTypes, p in Periods)
    ctUnderMaxDemand: Sell[c][p] <= MaxDemand[c][p];
     

  //制約2:各期のコンピュータータイプごとの販売台数が最小需要数以上
  forall(c in ComputerTypes, p in Periods)
    ctOverMinDemand: Sell[c][p] >= MinDemand[c][p];
      
  //制約3:各期のコンピュータータイプごとの在庫数が、各コンピュータータイプ毎の最大在庫数以下
  forall(c in ComputerTypes, p in Periods)
    ctComputerTypeInventoryCapacity:     
      InStockAtEndOfPeriod[c][p] <= Computers[c].maxInventory;

  //制約4:各期の組立台数が最大組立数以下　**hkwd追加
  forall(p in Periods)
    ctUnderMaxBuild:sum(c in ComputerTypes) Build[c][p] <= MaxBuildPerPeriod[p];
      
  //制約5:各期のコンピュータータイプごとの組立台数が全期の総組立台数と等しい
  forall(c in ComputerTypes)
    ctTotalToBuild:      
      sum(p in Periods) Build[c][p] == TotalBuild[c];

  //制約6:各期のコンピュータータイプごとの売上台数が全期の総組立台数と等しい。売り切らないと前モデルの目的関数の利益を達成できない　**hkwd追加
  forall(c in ComputerTypes)
    ctTotalToSell:      
      sum(p in Periods) Sell[c][p] == TotalBuild[c];    

  //制約7:1期目の組立台数が1期目の販売数と1期目の在庫数の合計と等しい
  forall(c in ComputerTypes)
    ctInventory1wBalance:      
    Build[c][1] == Sell[c][1] + InStockAtEndOfPeriod[c][1];
     
  //制約8:2期目以降の組立台数および前期の在庫数が、その期の販売数とその期の在庫数の合計と等しい
   forall(c in ComputerTypes, p in 2..NbPeriods)
     ctInventoryBalance:      
       InStockAtEndOfPeriod[c][p-1] + Build[c][p] == 
         Sell[c][p] + InStockAtEndOfPeriod[c][p]; 
}
