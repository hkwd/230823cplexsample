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

/***********************************************************************
* OPL Model for Staffing Example
* 
* This model is described in the documentation. 
* See "IDE and OPL > Language and Interfaces Examples > OPL model library" 
*
* This model is greater than the size allowed in trial mode. 
* You therefore need a commercial edition of CPLEX Studio to run this example. 
* If you are a student or teacher, you can also get a full version through
* the IBM Academic Initiative.
*************************************************************************/

/*
スタッフの割り当て

レストランは月曜日から金曜日まで、午前 8 時から午後 8 時まで営業しています。各勤務日は、次の 3 つの 4 時間シフトに分かれています。

朝食: 午前 8 時から午後 12 時
昼食: 午後 12 時から午後 4 時
夕食: 午後 4 時から午後 8 時

各シフトには、調理人、レジ係、清掃員の 3 種類の人員が必要です。
各人員は、これらのタスクの一部を実行できます。
一部の人は、特定の日に勤務できない場合があります。スケジュールされている場合、各人は 1 日 8 時間 (この場合は 2 シフト) 勤務し、シフトが連続していることを希望します。また、夜勤で勤務する場合、翌日の朝勤には勤務したくないと考えています。

目標は、空きスロットの合計数を最小化する、シフトへの従業員の適切な割り当てを見つけることです。
*/
  
//**************************** Data **************************************
int Totalshifts = ...; // １日あたりの総シフト数
int Nbshifts = ...;    // １日あたりに一人が働けるシフト数
range Shifts = 1..Totalshifts; 

{string} Skills = ...;     // スキル
{string} Weekdays = ...;   // 労働曜日 


int Req[Weekdays][Shifts][Skills] = ...;  // 各シフトに必要なスキルタイプの人数
          
{string} People = ...;     // 人員       
// Data Structure
tuple shift {
  key string p;
  string w;
}

tuple PSkill {
  key string p;
  {string} s;
}

{PSkill} PeopleSkills = ...; //  各人が持つスキルのリスト 
{shift}  Unavailable = ...;  // 各人の出勤不可曜日

int Penalty = card(Weekdays)*Nbshifts+1; // 未割当シフトに対するペナルティ

//********************************* 決定変数 **********************************
        
dvar boolean Assign[Weekdays][Shifts][People][Skills];   // シフト割り当てを示します
dvar int Unfilled[Weekdays][Shifts][Skills] in 0..maxint;  // 割当要求人数を満たさないシフト
dvar boolean Start[Weekdays][Shifts][People];             // 各人各日の勤務の最初のシフト



/************************************* Model *********************************/
// the total # of slots unfilled in a week
// 割当要求人数を満たさないシフトの総数
dexpr int TotUnfilled  =
  sum(w in Weekdays, s in Shifts, j in Skills) Unfilled[w][s][j];

//作業者のシフトが偏らないようにする。各人員に割り当てられたシフト数の最大差
dexpr int PAssign[p in People] = sum(w in Weekdays, s in Shifts, j in Skills) Assign[w][s][p][j];  
dexpr int Pdiff = max(p in People) PAssign[p] - min(p in People) PAssign[p];

minimize TotUnfilled*Penalty + Pdiff;
// Note:  ペナルティは、各人員に割り当てられたシフト数の最大差よりも高いため、スケジュールは常に最初に需要を満たし、次に作業負荷のバランスをとります。

subject to {
   
  // 制約１: 一日のシフトが２シフトである場合、連続である必要があります。朝と夜のシフトのような間を飛ばしたシフトは不可です
  // シフトが連続すること。シフトk中の人員の数 = kとk-1シフトの開始人員の合計数。
  forall(w in Weekdays, s in Shifts)   
      ct01_1:
      sum(p in People, j in Skills) Assign[w][s][p][j] == sum(i in Shifts: s-Nbshifts+1 <= i <= s, j in People) Start[w][i][j];
               
  forall(w in Weekdays, s in Shifts,p in People) {
    // ある人がシフト k で開始した場合、その人は次の nbshifts シフトで勤務可能になります。 
    forall(k in Shifts: s-Nbshifts+1 <= k <= s) 
      ct01_2:
      sum(j in Skills) Assign[w][s][p][j] >= Start[w][k][p];
    // 開始は連続できない。人がすでに開始している場合は、次の nbshifts シフトのいずれでも再度「開始」することはできません。 
    forall(k in Shifts: s+1 <= k <= s+Nbshifts-1) 
      ct01_3:
      1-Start[w][s][p] >= Start[w][k][p];
  }
   
    
    
  // In each shift,  # of people assigned to a type of task +
  //   unfilled slot >= # of people of that type required
  // 制約８:各シフトにおいて、あるタイプのタスクに割り当てられた人数 + 空いているスロット >= そのタイプの必要な人数 （必要な人数を満たしてなくてもよい ）
  forall(w in Weekdays, s in Shifts, j in Skills)
    ct08Unfilled:    
      sum(p in People) 
        Assign[w][s][p][j] + Unfilled[w][s][j] >= Req[w][s][j];

  // 制約６:人員によってできる仕事が異なります。料理人、会計係両方できる人もいますし、どちらかだけできる人もいます  
  forall(w in Weekdays, s in Shifts, t in PeopleSkills, k in Skills: k not in t.s)
    ct06:
    Assign[w][s][t.p][k] == 0;
        
  // 制約２:一日の間に２シフト以上連続では働けません
  forall(w in Weekdays, p in People) 
    ct02Shifts:      
      sum(s in Shifts, j in Skills) 
        Assign[w][s][p][j] <= Nbshifts;
        
  // 制約７:一部の人員は特定の曜日に労働できないことがあります
  forall(<p,w> in Unavailable, s in Shifts, j in Skills)
    ct07:
    Assign[w][s][p][j] == 0;
  
  // Each person can take only one task in each shift     
  // 制約４:一人の人が一つのシフト内でできる仕事は料理人、会計係のどちらかのみです     
  forall(w in Weekdays, s in Shifts, p in People) 
    ct04Tasks:      
      sum(j in Skills) 
        Assign[w][s][p][j] <= 1;
 
  // If a person is on a night shift, he cannot be assigned to the morning
  //  shift the next day
  // 制約３:夜のシフトで労働する人は、翌日の朝のシフトで労働しません
  forall(p in People, k in Skills) {
    ct03_1:   
    Assign["Tue"][1][p][k] <= 1 - sum(j in Skills) Assign["Mon"][Totalshifts][p][j];
    ct03_2:   
    Assign["Wed"][1][p][k] <= 1 - sum(j in Skills) Assign["Tue"][Totalshifts][p][j];
  }
  
  //Each shift has at least a cook, a cleaner and a cashier
  //制約５:各シフトには、料理人、会計係が最低一人は必要です
  forall(w in Weekdays, s in Shifts, j in Skills) 
    ct05Skills:
      sum(p in People) Assign[w][s][p][j] >= 1;     
}
