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

/* ------------------------------------------------------------

Problem Description
-------------------

This is a problem of building five houses in different locations. The
masonry, roofing, painting, etc. must be scheduled. Some tasks must
necessarily take place before others and these requirements are
expressed through precedence constraints.

There are two workers, and each task requires a specific worker.  The
time required for the workers to travel between houses must be taken
into account.  

Moreover, there are tardiness costs associated with some tasks as well
as a cost associated with the length of time it takes to build each
house.  The objective is to minimize these costs.


これは、異なる場所に 5 つの家を建てるという問題です。 石積み、屋根葺き、塗装などをスケジュールする必要があります。 
一部のタスクは必ず他のタスクより前に実行する必要があり、これらの要件は優先順位の制約によって表現されます。

ワーカーは 2 人おり、各タスクには特定のワーカーが必要です。 
作業員が家の間を移動するのに必要な時間を考慮する必要があります。

さらに、一部のタスクに関連する遅延コストや、各家を建てるのにかかる時間の長さに関連するコストも発生します。 
目的は、これらのコストを最小限に抑えることです。

------------------------------------------------------------ */

//制約プログラミング
using CP;

//住宅の軒数
int NbHouses = ...; 
range Houses = 1..NbHouses;

//作業者名のセット
{string} WorkerNames = ...;  
//タスク名のセット
{string} TaskNames   = ...;

//タスク所要日数の配列
int    Duration [t in TaskNames] = ...;
//タスクに割り当てられた作業者
string Worker   [t in TaskNames] = ...;

//タスクの前後関係のタプルセット
tuple Precedence {
   string pre;
   string post;
};

{Precedence} Precedences = ...;

//住宅建設の最短開始可能日
int   ReleaseDate[Houses] = ...; 
//住宅建設の終了希望日
int   DueDate    [Houses] = ...; 
//終了希望日以降の1日当たりの遅延ペナルティコスト
float Weight     [Houses] = ...; 

//住宅(type)から住宅(type)への移動必要日数
tuple triplet { int type1; int type2; int value; }; 
{triplet} transitionTimes = { <i,j, ftoi(abs(i-j))> | i in Houses, j in Houses };


////決定変数
//各住宅の各タスクの間隔変数。サイズの所要日数の指定がある。これで制約1の「各タスクにはそれぞれ所要日数があり、連続して行う必要がある」が制約される
dvar interval itvs  [h in Houses][t in TaskNames] size Duration[t];
//各住宅の間隔変数。スタートは開始可能日以降。これで制約2の「各住宅は開始可能日以降に建設を開始する必要がある」が制約される
dvar interval houses[h in Houses] in ReleaseDate[h]..(maxint div 2)-1;
//作業者のシーケンス変数。各作業者毎に各住宅の、実行可能な各タスクを割り当てる。これで制約3「各タスクは担当作業者が行う」が制約される。ここではｔypeは住宅番号をあらわしている
dvar sequence workers[w in WorkerNames]
    in all(h in Houses, t in TaskNames: Worker[t]==w) itvs[h][t]
    types all(h in Houses, t in TaskNames: Worker[t]==w) h;


/*
//失敗回数の設定
execute {
  cp.param.FailLimit = 30000;
}
*/

//時間制限の設定
execute{
		cp.param.timeLimit=60;
}

////目的関数
//各住宅の建設日数＋終了希望日からの遅延日数＊ペナルティコストの合計が最小
minimize sum(h in Houses) 
  (lengthOf(houses[h]) +  maxl(0, endOf(houses[h])-DueDate[h]) * Weight[h]);

////制約
subject to {
  //制約4: 各タスクの前後関係が守られている

  forall(h in Houses)
    forall(p in Precedences)
      ctPrecedence:
      endBeforeStart(itvs[h][p.pre], itvs[h][p.post]);

  //制約5,6:一人の作業者のタスクは1時点で一つのみ、住宅から住宅へ作業者が移動する場合にはそれぞれの移動日数が発生するという制約

  forall(w in WorkerNames)
    ctWorker:
    noOverlap(workers[w], transitionTimes);


  //制約7:家の間隔変数内にその家のタスクの間隔変数があるという制約
  forall(h in Houses)
    ctHouse:
    span(houses[h], all(t in TaskNames) itvs[h][t]);


}

//結果データ出力
//最終終了日
int endOfAll = max(h in Houses) endOf(houses[h]);
//遅延ペナルティコスト
float penalties[h in Houses] = maxl(0, endOf(houses[h])-DueDate[h]) * Weight[h];


execute {
  writeln("endOfAll: " + endOfAll);
  
  writeln("Penalties");
  for(h in Houses){
    writeln("house"+h+": "+penalties[h]);
  }    
}

/*
OBJECTIVE: 13852
*/
