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

// CLP model from the paper 
//
// Algorithms for hybrid MILP/CLP models for a class of optimization problems
// Vipul Jain and Ignacio Grossmann
// 
// Department of Chemical Engineering, Carnegie Mellon University
// 5000 Forbes Avenue, Pittsburgh, PA 15213, United States
//
// http: egon.cheme.cmu.edu/
// email: vjain@andrew.cmu.edu, ig0c@andrew.cmu.edu

// The data is given in separate files, the equation numbers refer to the paper
//制約プログラミング
using CP;

// マシン台数 (Packing + Manufacturing)
int nbMachines = ...;
range Machines = 1..nbMachines;

// ジョブ数
int nbJobs = ...;
range Jobs = 1..nbJobs;

//　開始可能日
int release [Jobs] = ...;
//　締切日
int due     [Jobs] = ...;

// 所要時間
int duration[Jobs,Machines] = ...;
// コスト
int cost    [Jobs,Machines] =...;
 
//ジョブ。開始可能日と締切日がある
dvar interval job[j in Jobs] in release[j]..due[j];
//マシンに割り当てられたジョブ
dvar interval assignedJobToMachine[j in Jobs][m in Machines] optional size duration[j][m];
//マシンに割り当てられたジョブの順序
dvar sequence machine[m in Machines] in all(j in Jobs) assignedJobToMachine[j][m];

//失敗回数の設定
execute {
		cp.param.FailLimit = 5000;
}


// Minimize the total processing cost (24)
// 総処理コストを最小限に抑える（24）
minimize 
  sum(j in Jobs, m in Machines) cost[j][m] * presenceOf(assignedJobToMachine[j][m]);
subject to {
  // Each job needs one unary resource of the alternative set s (28)
  //制約2:各ジョブはマシンのどちらかに割り当てる
  forall(j in Jobs)
    ct1_AssignOneOfTheMachneToTheJob:
    alternative(job[j], all(m in Machines) assignedJobToMachine[j][m]);
  
  // No overlap on machines
  // 制約3:マシンのスケジュールは重複しない
  forall(m in Machines)
     ct2MachineSchedulesNoOverlap:
     noOverlap(machine[m]);
  
};

