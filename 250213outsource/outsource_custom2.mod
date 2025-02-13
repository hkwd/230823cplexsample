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

/**************************************************************
Outsourcing Example

This model is described in the documentation. 
See IDE and OPL > Language and Interfaces Examples.
   
**************************************************************/

{string} Items = ...;
{string} Suppliers = ...;
{string} AUDsuppliers = ...; // AUD（全単位割引）サプライヤー
{string} CQDsuppliers = ...; // CQD（増分割引）サプライヤー 

assert card(CQDsuppliers union AUDsuppliers) == card(Suppliers);

int ItemDemand[Items] = ...; // 各アイテムの需要数
int TotalSupplierCap[Suppliers] = ...; // 各サプライヤーの全品目の供給能力
int MaxN = sum(i in Suppliers) TotalSupplierCap[i];// 全供給能力

int SetupCost[Suppliers] = ...; // サプライヤー毎のセットアップコスト

int NumAmts = ...; // 数量レンジの数
range Amts = 1..NumAmts; // 数量レンジのインデックス
int BreakAmts[1..NumAmts+1] = ...; // 数量レンジ
float CostInRanges[Items][Suppliers][Amts] = ...; //数量レンジ毎の単価



// 決定変数
// 各アイテム、各サプライヤーへの数量レンジ毎の発注量
dvar int Quantity[Items][Suppliers][Amts] in 0..MaxN;
// 各アイテム、各サプライヤーへの価格レンジ毎の発注のありなしフラグ
dvar int SupAmt[Items][Suppliers][Amts] in 0..1;
// 各サプライヤーへの発注のありなしフラグ
dvar int Setup[Suppliers] in 0..1;

// 決定式
// ①総発注コスト
dexpr float TotalVariableCost =
  sum(i in Items, s in Suppliers, a in Amts) CostInRanges[i][s][a] 
                                                 * Quantity[i][s][a];
// ②総セットアップコスト
dexpr float TotalSetupCost =
  sum(s in Suppliers) SetupCost[s]*Setup[s];                                            


// 目的関数：①総発注コスト+②総セットアップコストの合計を最小化
minimize TotalVariableCost + TotalSetupCost;

// 制約                                              
subject to {
  // 各サプライヤーの供給能力以内
  forall(s in Suppliers)
    ct01Caps: sum(i in Items, a in Amts) Quantity[i][s][a] <= TotalSupplierCap[s];
       
  // 各アイテム需要量を満たす
  forall(i in Items)
    ct02Dem: sum(s in Suppliers, a in Amts) Quantity[i][s][a] >= ItemDemand[i];
      
  // 全ユニット割引サプライヤーは、各品目に対して1つの価格レンジのみ
  forall(i in Items, s in AUDsuppliers)
    ct03:
    sum(a in Amts) SupAmt[i][s][a] == 1;
        
  // 全ユニット割引サプライヤーは、発注量に応じた正しい価格レンジの単価を適用する
  forall(i in Items, s in AUDsuppliers, a in Amts) {
    // ある数量レンジの発注量は、その次数量レンジの数量-1以下になる
    // 例えば、100－200個のレンジ内の数量の発注は199個以下。
    ct04_1:
    Quantity[i][s][a] <= (BreakAmts[a+1]-1) * SupAmt[i][s][a];
    // ある数量レンジの発注量は、数量レンジの数量以上になる
   // 例えば、100－200個のレンジ内の数量の発注は100個以上。
    ct04_2:
    Quantity[i][s][a] >= (BreakAmts[a]) * SupAmt[i][s][a];
  }
   
  //増分割引サプライヤーは発注量に応じた数量レンジ内の数量の増分ごとの単価を適用する
  forall(i in Items, s in CQDsuppliers, a in Amts) {
    ct05_1:
    forall(k in 1..a-1) {
      // ある数量レンジを超える発注量がある場合は、それ以下の数量レンジへの発注数は、各数量レンジ区間の数量になる
      // 例えば、0-100個は単価100円、100－200個は単価90円で、150個発注する場合、0-100個のレンジに対する発注は100個になる。
      // Because the "quantity" for CQDs is incremental, if CQD order quantity lies 
      // in discount interval a, namely, sup[i,s,a]=1, then
      // the quantities in interval 1 to a-1, should be the length of those ranges.  
      Quantity[i][s][k] >= (BreakAmts[k+1]-BreakAmts[k])*SupAmt[i][s][a];      
    }
    // 各数量範囲の発注量は、数量レンジ区間の数量以下である      
    ct05_2:
    Quantity[i][s][a] <= (BreakAmts[a+1]-BreakAmts[a])*SupAmt[i][s][a];            
  }


  //サプライヤーにいずれかのアイテムを発注すると、セットアップコストが発生する
  forall(s in Suppliers) 
    ct06Setup: Setup[s]*MaxN >= sum(i in Items, a in Amts) Quantity[i][s][a];

}

//発注サマリー表示
int TotalQuantity[i in Items][s in Suppliers] = sum(a in Amts)(Quantity[i][s][a]);

execute DISPLAY {
   writeln("TotalQuantity = ", TotalQuantity);
}
