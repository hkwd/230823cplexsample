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
OPL Model for Computer Assembly Line Sequencing Example 

This model is to determine the processing order of a set of custom 
computers on an assembly line. Once the order is assigned, 
it is kept from start to finish.  The custom computers have 
different lists of components to be contained, which are given 
in the array "computer".  

The ordering of the computers is constrained by the assembly 
rules of each component:  
1) There must be a minimum number of computers in a row 
   that need this component ("minSeq"); 
2) There is an upper bound on the number of computers in a row 
   that can have that component;  
3) Each component also has a list of illegal followers 
   ("illegalFollowers") meaning that if a computer has this 
   component, then the next computer cannot have a component 
   that appears in the illegal followers list of this component.  
These restrictions may be due to set-up times, bottlenecks, etc.

*/
/*
アセンブリの順序付け

製造サンプル：組み立てスケジューリング
https://www.ibm.com/docs/ja/icos/20.1.0?topic=library-manufacturing#usroplsamples.uss_opl_modlib.1016611__usroplsamples.uss_opl_modlib.1031132

このモデルは、組立ラインで処理される一連のカスタム コンピューターの順序を決定するためのものです。 
一度割り当てられた順序は、最初から最後まで保持されます。 
カスタム コンピューターには、含まれる部品のさまざまなリストがあり、配列「コンピューター」で指定されます。

コンピューターの順序は、各部品の次の組み立て規則によって制限されます。

1) この部品 (「minSeq」) を必要とするコンピューターの最小数が連続して存在する必要があります。
2) その部品を保持できる連続したコンピュータの数には上限があります。
3) 各部品には、不正なフォロワーのリスト (「illegalFollowers」) も含まれているため、
次のコンピュータは、この部品の不正なフォロワー リストに表示される部品を持つことができません。

これらの制限は、セットアップ時間やボトルネックなどが原因である可能性があります。


この例を実行するにはどうすればよいでしょうか?
   * CPLEX Studio IDE で、サンプル「Assembly Sequencing」をインポートします。
実行構成「基本構成」を右クリックし、「これを実行」を選択します。
   * コマンド ラインで、「oplrun -p <インストール ディレクトリ>\opl\examples\opl\models\AssemblySequencing」を実行します。


----------------------------------------------------- */
using CP;


execute{
	}

// The number of computers we need to build
// 組み立てる必要があるコンピューターの台数
int     nComputers  = ... ;
range   AllComputers = 1..nComputers ;

// 部品タイプのセット
{string} ComponentTypes = ...;

//組み立てルール（最大連続、最小連続、不正なフォロワーのセット）のタプル
tuple ComponentInfo
{
   int maxSeq;
   int minSeq;
   {string} illegalFollowers;
};

// Assembly rules for each component 
// 各部品の組み立てルールのタプルの配列
ComponentInfo    components[ComponentTypes]  = ...;

// List of components needed by a computer
// コンピュータに必要な部品のセットのリスト
{string} computer[AllComputers] = ...;
//全てのコンピューターの部品がComponentTypesで定義されているかの確認
assert {
   forall (a in AllComputers)
     forall (s in computer[a])
        s in ComponentTypes;
}

// Components that are actually in computers to build
// 実際に実際にコンピュータに利用されている部品のセット
{string} UsedComponentTypes = { c | c in ComponentTypes, a in AllComputers : c in computer[a] };
// 全ての利用部品がComponentTypesで定義されているかの確認
assert {
   forall (u in UsedComponentTypes)
      u in ComponentTypes;
}

// Components that have illegal followers
// 不正なフォロワーを持つ部品
{string} HasIllegalFollowers = { c | c in UsedComponentTypes, d in UsedComponentTypes 
                                     : d in components[c].illegalFollowers };
//{string} HasIllegalFollowers = { c | c in UsedComponentTypes: c in components[c].illegalFollowers };
// 不正なフォロワーを持つ部品がComponentTypesで定義されているかの確認
assert {
   forall (u in HasIllegalFollowers)
      u in ComponentTypes;
}                                     
// Which computers contain the component
// 各部品がどのコンポーネントで利用されているかのセット
{int}  componentInComputer[c in UsedComponentTypes] = {i | i in AllComputers : c in computer[i] };

// componentInComputerに結びつくコンピューターが定義されているかの確認
assert {
   forall (c in UsedComponentTypes)
      forall (u in componentInComputer[c]) {
         u >=1;
         u <= nComputers;
      }
}


/*  ----------------------------------------------------
 *   Variables:
 *   computerInSeq -- if computerInSeq[i]=j, it means computer[j] is ith in the 
 *          sequence
 *   決定変数:
 *   組立順序-- computerInSeq[i]=j の場合、 組立順序内で[i] 番目のコンピュータがjであることを意味します
 *   --------------------------------------------------- */
dvar int computerInSeq[1..nComputers] in AllComputers;

/*  ----------------------------------------------------
 *   Constraints
 *   制約
 *   --------------------------------------------------- */

subject to
{
   // 制約0:コンピューターはすべて異なる
   ct0allDifferent:
   allDifferent(computerInSeq);


   // 制約1:最大連続
   forall (c in UsedComponentTypes) {
      forall ( p in 1..nComputers - components[c].maxSeq )
         // If there are maxSeq # of component c in a row starting from position p to p+maxSeq-1, 
         // => the (p+ maxSeq)th computer must not contain component c.  
         // 位置 p から p+maxSeq-1 までの行に部品 c の maxSeq # がある場合、
         // => (p+ maxSeq) 番目のコンピューターには部品 c が含まれていてはなりません。
         // ct1:
         (sum(s in p..p+components[c].maxSeq-1) (computerInSeq[s] in componentInComputer[c]) == components[c].maxSeq) 
         => 
         //not (computerInSeq[p+components[c].maxSeq] in componentInComputer[c]);
         computerInSeq[p+components[c].maxSeq] not in componentInComputer[c];
   };   
   // 制約2-1:1 番目のコンピューターの部品は、少なくとも minSeq # 回連続して出現する必要があります。
   forall (c in UsedComponentTypes) {
      // The components in the 1st computer must appear at least minSeq # of times in a row.   
      // 1番目のコンピューターの最小連続の制約
      ct2firstComponentHigherThanMinseq:
      (computerInSeq[1] in componentInComputer[c]) 
      => 
      ((sum( s in 1..components[c].minSeq) (computerInSeq[s] in componentInComputer[c])) >= components[c].minSeq);
   }   
   // 制約2-2:2番目以降のコンピューターの最小連続の制約
   forall (c in UsedComponentTypes) {
      forall ( p in 1..nComputers-components[c].minSeq )
            // Every component that is not in computer p but appears in computer p+1
            // must appear minSeq # of times in a row from p+1 to p+minSeq.  
            // コンピューター p には存在しないが、コンピューター p+1 に表示されるすべての部品
            // minSeq は p+1 から p+minSeq まで連続して何回も出現する必要があります。
            //ct3:
            (((computerInSeq[p] not in componentInComputer[c])
               && (computerInSeq[p+1] in componentInComputer[c])) =>
            (sum(s in p+1..p+components[c].minSeq) (computerInSeq[s] in componentInComputer[c]))
                 == components[c].minSeq);
   };

   // 制約3:各部品に、不正なフォロワー (「illegalFollowers」)がある場合、次の組立では、その不正な部品は含まれてはならない。
   forall (c in HasIllegalFollowers) // for component c that has an illegal follower,不正なフォロワーを持つ部品 c の場合
      forall( p in 1..nComputers-1)  // for computer p コンピュータ用
         forall( c2 in UsedComponentTypes : c2 in components[c].illegalFollowers) 
            // If computer p has component c and c2 is c's illegal follower => 
            // c2 must not be in computer p+1 
            // コンピューター p に部品 c があり、c2 が c の不正なフォロワーである場合 =>
            // c2 はコンピュータ p+1 にあってはなりません
            ct4illegalfollower:
            (computerInSeq[p] in componentInComputer[c] )  =>
               (computerInSeq[p+1] not in componentInComputer[c2]);
               
};

