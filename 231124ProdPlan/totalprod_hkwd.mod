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
 * This model is described in the documentation. 
 * See IDE and OPL > Language and Interfaces Examples.
　* https://www.ibm.com/docs/ja/icos/20.1.0?topic=library-manufacturing#usroplsamples.uss_opl_modlib.1016611__usroplsamples.uss_opl_modlib.1016871

このモデルは、コンピューター組み立て工場の生産計画を説明するものです。この工場は、MultimediaBusiness、MultimediaHome、および BasicHome という 3 つのコンピューター・モデルを組み立てることができます。
組み立ては、CPU やモデムなどのコンポーネントを適切なコンピューターに取り付けることで構成されます。このモデルでは、以下の 2 つのステップを示しています。

1. 組み立てる各タイプのコンピューターの総数と、必要なコンポーネントを取得する場所を決定します。(totalprod_hkwd.mod)
2. 組み立てるコンピューターの数を決定したら、各期間に組み立てる数、販売する数、および在庫として保持する数を決定します。(period_hkwd.mod)
 *   --------------------------------------------------- */
 
// コンピュータータイプとコンポーネントの定義
{string} ComputerTypes = ...;
{string} ComponentTypes = ...;

//int NumComputerTypes = card(ComputerTypes);

/*   ---------------------------------------------------
 *   Each computer type has a list of components, a 
 *   selling price and a maximum on the number allowed 
 *   to be held over in inventory to the next period.
 各コンピュータタイプには、コンポーネントのリスト、販売価格、および在庫可能最大数があります。
 *   --------------------------------------------------- */
tuple computersToBuild
{
  {string} components;
  int      price;
  int      maxInventory;
}

computersToBuild Computers[ComputerTypes] = ...;

// Number of Periods to use for this problem
// 期間数
int NbPeriods = ...;
range Periods = 1..NbPeriods;



/*   ---------------------------------------------------
 *   Each computer type has a maximum and minimum amount
 *   that can be sold in each period.  These values are
 *   used to calculate a range on the total to build of
 *   each computer type.  There is also a plant capacity
 *   for each period.
 各コンピューターの種類には、各期間に販売できる最大数量と最小数量があります。 これらの値は、各コンピューターの種類の合計構築範囲を計算するために使用されます。 各期間のプラント容量もあります。
 *   --------------------------------------------------- */
//期ごとの最大の組立可能数
int MaxBuildPerPeriod[1..NbPeriods] = ...;

//コンピュータの種類と期ごとの最小最大の需要量
int MinDemand[ComputerTypes][1..NbPeriods] = ...;
int MaxDemand[ComputerTypes][1..NbPeriods] = ...;



//全期分の最大組立数
int MaxBuild = 0;
//コンピュータの種類ごと全期分の最小最大の需要量
int TotalMaxDemand[ComputerTypes];
int TotalMinDemand[ComputerTypes];
//未使用float TotalBuild[ComputerTypes];
//for文で初期化
execute INITIALIZE {
  for(var p in Periods) {
    MaxBuild = MaxBuild + MaxBuildPerPeriod[p];
    for(var c in ComputerTypes) {
      TotalMaxDemand[c] = MaxDemand[c][p] + TotalMaxDemand[c];
      TotalMinDemand[c] = MinDemand[c][p] + TotalMinDemand[c];
    }
  }
}

//部品サプライヤー
{string} Suppliers = ...;
//サプライヤーのコスト変化ポイントの定義
int NbCostChanges = ...;         // 区分線形のブレイク数　Number of "breaks" in PLF
int SupplyCostCostChanges[1..NbCostChanges] = ...;
//未使用range CostChangespp = 1..NbCostChanges+1;

//コンポーネントのタイプ毎、サプライヤーごとのコストの傾斜
tuple componentInfo
{
  string supplier;
  int    costSlope[1..NbCostChanges+1];   //CostChangesppと同じであるべき。should be CostChangespp
}
{componentInfo} Components[ComponentTypes] = ...;

tuple supplierMatch {
  string         component;
  componentInfo  componentInformation;
}
{supplierMatch} ComponentSupplierMatches = { <i,j> | i in ComponentTypes, j in Components[i] };


////決定変数
/*  ----------------------------------------------------
 *   Variables:
 *   build --   How many of each computer type to build.
 *   NecessaryComponents -- Based on build
 *   SuppliedComponents -- How many of each component
 *         type are supplied by which supplier
 *   inHouse -- How many of each component type are
 *         manufactured in House.
 *   grossProfit -- linear function of build
 *   cost -- function of SuppliedComponents and inHouse
 *   --------------------------------------------------- */

//組立数 -- 各タイプのコンピューターを何台組み立てるか。
//dvar float+ Build[ComputerTypes];
dvar int+ Build[ComputerTypes];
//必要な各コンポーネント数 -- Buildに基づく 
//dvar float+ NecessaryComponents[ComponentTypes];
dvar int+ NecessaryComponents[ComponentTypes];
//コンポーネント供給数 -- 各コンポーネント タイプがどのサプライヤーによっていくつ供給されるか。
//dvar float+ SuppliedComponents[ComponentSupplierMatches];
dvar int+ SuppliedComponents[ComponentSupplierMatches];
/*
//内製コンポーネント数 -- 各コンポーネント タイプのいくつを社内で製造するか。　//
dvar float+ InHouse[ComponentTypes];
*/

////決定式
//コスト -- SuppliedComponents と inHouse 
dexpr float Cost =       
  sum(m in ComponentSupplierMatches)
    piecewise(i in 1..NbCostChanges) {
      m.componentInformation.costSlope[i] -> SupplyCostCostChanges[i];   
      m.componentInformation.costSlope[NbCostChanges+1]
    } SuppliedComponents[m];
    
//売上 -- ビルドの線形関数
dexpr float Sales=
  sum(p in ComputerTypes) Computers[p].price * Build[p];

//粗利益
dexpr float GrossProfit = Sales - Cost;

////目的関数 粗利益の最大化
//minimize Cost-GrossProfit;

maximize GrossProfit;

////制約
/*  ----------------------------------------------------
 *   constraints
 *   --------------------------------------------------- */
subject to
{
  //制約1: 各コンピューターは最大組み立て数以下
  ctPlantCapacity:
    sum(p in ComputerTypes) Build[p] <= MaxBuild;
      
  //制約2:各コンピューターは最大需要数以下
  //制約3:各コンピューターは最小需要数以上
  forall(p in ComputerTypes){
    ctComputerTypeMaxDemand: Build[p] <= TotalMaxDemand[p];
    ctComputerTypeMinDemand: Build[p] >= TotalMinDemand[p];      
  }  


  // Get the necessary components
  //制約4:組み立てるコンピュータータイプの台数と必要なコンポーネント数が一致する
/*
  forall(c in ComponentTypes)
    ctDetermineAmtNecessary:      
      sum(p in ComputerTypes: c in Computers[p].components) 
        Build[p] == NecessaryComponents[c];
*/
  forall(c in ComponentTypes)
    ctDetermineAmtNecessary:      
      sum(p in ComputerTypes: c in Computers[p].components) 
        Build[p] == NecessaryComponents[c];
         
 //制約5:供給されるコンポーネント数と必要なコンポーネント数が一致する
  forall(c in ComponentTypes)
    ctDetermineAmtSupplied:      
      sum(m in ComponentSupplierMatches: c == m.component) 
         SuppliedComponents[m] == NecessaryComponents[c];
 
/*
//自社供給されるコンポーネント数とコンポーネント供給数が一致する
  forall(m in ComponentSupplierMatches: m.componentInformation.supplier == "InHouse")
    ctMadeInHouse:      
      InHouse[m.component] == SuppliedComponents[m];
*/         
}

main {

/*   ---------------------------------------------------
 *   Solve the first model.  This piecewise-linear 
 *   program determines the total number of each computer 
 *   type to build, as well as from where to acquire the 
 *   necessary components.  The objective is to 
 *   maximize profit (really, minimize -profit).
 *   The quantity.build var values are stored to use in
 *   the second step.
 最初のモデルを解きます。 この区分線形プログラムは、構築する各コンピューター タイプの合計数と、必要なコンポーネントをどこから入手するかを決定します。 
 目的は、利益を最大化することです (実際には、利益を最小化することです)。
　quantity.totalbuild 変数値は、2 番目のステップで使用するために保存されます。
 *   --------------------------------------------------- */

   //数量決定モデルの設定
   var quantity = thisOplModel;
   quantity.generate();
   if (cplex.solve()) {

     var c;   
     var m; 
     var totalbuild = new Array();

     //粗利益出力
     writeln("Gross profit: ", cplex.getObjValue());
     // Output & get total to build of each type
     // 各コンピュータータイプ毎の組立台数の合計を算出して出力
     for(c in quantity.ComputerTypes) {
       totalbuild[c] = quantity.Build[c].solutionValue;
       writeln("   ", c, ":  ", totalbuild[c]);
     }
     //内製で生産するコンポーネント
     writeln("Components to build in-house:");
     for(m in quantity.SuppliedComponents){
       if(quantity.SuppliedComponents[m] > 0 
       && m.componentInformation.supplier == "InHouse") {
         writeln("  ", m.component, ": ", quantity.SuppliedComponents[m].solutionValue);
       }
    }      

    /*
     for(c in quantity.ComponentTypes){
       if(quantity.InHouse[c] > 0) {
         writeln("  ", c, ": ", quantity.InHouse[c].solutionValue);
       }
    }      
    */

     /*   ---------------------------------------------------
      *   Solve the second model.  This linear program
      *   determines the number of each computer type to
      *   build, sell and hold in each period.  The 
      *   objective is to find a feasible solution.
      2 番目のモデルを解きます。 この線形プログラムは、各期間に製造、販売、保持する各タイプのコンピューターの数を決定します。 
      目的は、実現可能な解決策を見つけることです。
      *   --------------------------------------------------- */

     // 期間最適化のモデル読込
     var source = new IloOplModelSource("period_hkwd.mod");
     var def = new IloOplModelDefinition(source);
     var newCplex = new IloCplex();
     var dates = new IloOplModel(def, newCplex);
     var data = new IloOplDataSource("period_hkwd.dat");
     dates.addDataSource(data);
     data = dates.dataElements;
     //モデル１の最適化結果でデータを書き換える。
     for(c in dates.ComputerTypes) {
       data.TotalBuild[c] = totalbuild[c];
     }
     dates.generate();
     if (newCplex.solve()) {
       // 出力　Output
       for(var p in dates.Periods) {
         writeln("Period: ", p)
         for(c in dates.ComputerTypes) {
           writeln("  ", c, ":  ")
           writeln("      Build: ", dates.Build[c][p].solutionValue)
           writeln("      Sell:  ", dates.Sell[c][p].solutionValue)
           writeln("      Hold:  ", dates.InStockAtEndOfPeriod[c][p].solutionValue)
         }
       }
     }
     dates.end();
   } else {
     writeln("Could not determine the total number of each computer type to build");
   }
}
