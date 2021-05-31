/* Maximum flow - highest lavel push-relabel algorithm */
/* COPYRIGHT C 1995, 2000 by IG Systems, Inc., igsys@eclipse.net */
  
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <values.h>
#include <math.h>

#include "types_treem.h"  /* type definitions */
#include "parser_treem.c" /* parser */
#include "timer.c"        /* timing routine */

#define MAX_LONG LONG_MAX

#define min(s, t) (s) < (t) ? (s) : (t)
#define max(s, t) (s) > (t) ? (s) : (t)

/////////////////////////////////////////
///////////////////////////////////////// The definition of data structure
/////////////////////////////////////////

//data structure that holds graph data
typedef
struct GraphData_{

  long N, M;
  nodeP *nodes;

} GraphData;


//data structure that holds data for randomrization
typedef
struct RandomData_{
  cType *randNums;
  cType randNumIdx;
} RandomData;


//data structure that holds preprocessing data
typedef
struct PreprocData_{

  //graph data
  GraphData *gd;

  //holds data in all passes
  NodePropArr* allResults;

  //pre-generated data
  RandomData* rd;

  //<BEING> hold the hot data in current pass
  cType *gpfa;
  cType *gpdep;
  long *gpcv;
  long *gpoh;
  long *gpcof;
  short *gps;
  cType *gpaccup;
  long *gpaccmcv;
  cType *gpaccposmcv;
  cType *gpaccjointid;
  long *gpaccjointmcv;
  //<END>

  cType *roots; //records root in each pass

  int mode; //the traversing mode, as explained in the paper

  int P; // P% percent of total passes in mode 1, the remaining in mode 2
  int total; //number of total passes
  int SPAN_LEN; //the length of a ancestor span, used for acceleration in traversal trees

} PreprocData;




///////////////////////////////////////////
///////////////////////////////////////////The definition of functions
///////////////////////////////////////////


//The function for allocation
void *walloc(unsigned int num, unsigned int size)
{
  void *ptr = calloc(num, size);
  assert(ptr != NULL);
  return ptr;
}

//The function for randomization
cType mrand(RandomData* rd)
{
  return rd->randNums[rd->randNumIdx++];
}

RandomData* initrand(cType len)
{
  RandomData *rd = walloc(1, sizeof(RandomData));

  srand((int)(timer() * 1000));

  rd->randNums = (cType *)walloc(len, sizeof(cType));
  rd->randNumIdx = 0;

  for (int i = 0; i < len; i++)
  {
    rd->randNums[i] = (cType)rand();
  }

  return rd;
}

/////////////////////////The two function for heap sorting edges 
void HeapAdjustDown(sType *idx, edgeP * edges ,int start,int end)  
{  
    sType tempIdx = idx[start];  

    int i = 2*start+1;      
    
    // assert(idx[0] != idx[3]);
    
    while(i<=end)  
    {  
        if(i+1<=end && edges[idx[i+1]].tmp > edges[idx[i]].tmp )    
            i++;  

        if(edges[idx[i]].tmp <= edges[tempIdx].tmp )   
            break;  

        idx[start] = idx[i];

        start = i;  
        i = 2*start+1;  
    }  

    idx[start] = tempIdx;  
}  
  
void HeapSort(sType *idx, edgeP * edges, int len)  
{  

    int i;  
    for(i=(len-1)/2;i>=0;i--){  
        HeapAdjustDown(idx,edges,i,len-1);  
    }

    for(i=len-1;i>0;i--)
    {  
        // printf("swap 0 with %d \n",i);
        sType temp = idx[i];  
        idx[i] = idx[0];  
        idx[0] = temp;  

        HeapAdjustDown(idx,edges,0,i-1);  
    }  

}  
  
/////////////////////The function to sort edges using capacity
void deOrderEdgeByRandomCap(nodeP *np,PreprocData *pd)
{

  cType cnt = np->nIdx;

  sType *idxs = np->orderedEdges;
  edgeP *pedges = np->edges;

  for (int i = 0; i < cnt; i++)
  {
    pedges[i].tmp = -1*mrand(pd->rd) % pedges[i].cap;
  }

    assert(cnt<4 || idxs[2]!=idxs[3]);
    HeapSort(idxs,pedges,cnt);
    assert(cnt<4 || idxs[2]!=idxs[3]);  
}

///////////////////The function to sort edges using the value of currently minimal cut one edge belongs to 
void aOrderEdgeByAvgCV(nodeP *np,PreprocData *pd)
{
  if (np->nIdx == 0)
  {
    return;
  }
  int cnt = np->nIdx;

  sType *idxs = np->orderedEdges;
  edgeP *pedges = np->edges;

  for (int i = 0; i < cnt; i++)
  {
    edgeP *pp = pedges +i;
    long acv = pp->avgCV;
    if(acv == 0 ){
      pp->tmp = MAX_LONG;
    }
    else{
      pedges[i].tmp = mrand(pd->rd) % acv; 
    }
  }

    HeapSort(idxs,pedges,cnt);
}


/*
  the function to add more data to a traversal tree to accelerate the searching in the tree
  The idea is to precalcuate minimal cv value of a span of nodes in a traversal tree, e.g., when SPAN_LEN = 100, and a node has depth of 200, then the algorithm will pre-calculate the minimal cv value of the nodes between the node (dep=200) and an acestor(dep=101)
  upid is the id of the last SPAN node, mcv is the min cv among all previous nodes in the recent SPAN
  lastDepMCV is the depth of the node depth that has the minimal cv in the span
  lastJointNodeId is the last ancestor node id that has more than one child nodes
  lastJointMCV is the cv of lastJoineNodeId

  改版后预处理算法要有变化：
      对每个节点的值，都要改进下考虑当前出发节点z的考虑下游分支的更小的cv'=cv2+-cof

  (1)处理时：
      在非段头节点中还要考虑父亲cv'的值，如果更小，则更新指向父亲
      跨段的cv2+-cof直接放到下段mcv中，因为solve中确认跨段了才使用当前段的mcv
  (2)求解时：
      看solve的注释


*/

long gRoot = 0;
void buildAcc(PreprocData *pd, cType curN, cType upid, long mcv, cType lastDepMCV,cType lastJointNodeId, long lastJointMCV)
{
  nodeP* nodes = pd->gd->nodes;
  assert(curN <= pd->gd->N && curN >= 1);
  int cnt = (nodes + curN)->nIdx;
  edgeP *pedges = (nodes + curN)->edges;

  long curCV = pd->gpcv[curN];
  cType curDep = pd->gpdep[curN];

  assert(curDep == 0 || curCV >0);

  //update using father's cv2(poh)- curN's cof
  long fcv2 = pd->gpoh[pd->gpfa[curN]];
  if(pd->gpcof[curN] < 0){
    //to keep current child and its tree, father cv2 need to increase a little by -cof_curN
    fcv2 = fcv2 - pd->gpcof[curN];
  }

  mcv = min (mcv, fcv2);
  if(pd->gpfa[curN] == upid){
    //it's the segment head 
    //can't update its father, which will be updated when solving
  }
  else{
    if(mcv == fcv2){
      //father is the minimal
      lastDepMCV = curDep-1;
    }

  }
//logic for span
  mcv = min(mcv, curCV);
  if(mcv == curCV){
    lastDepMCV = curDep;
  }

  //check father 
  if(mcv == 0 && curN != gRoot){
    printf("curN %ld 's paccmcv is 0,dep is %ld \n",curN,pd->gpdep[curN]);
    assert(1==2);
  }
  pd->gpaccmcv[curN] = mcv;
  pd->gpaccup[curN] = upid; //the previous segment tail
  pd->gpaccposmcv[curN] = curDep - lastDepMCV; //the diff of dep to curN in the segment, where is the node with minimal cv/cv2 keeping curN

  if (curDep % pd->SPAN_LEN == 0)
  {//the bottom of a segment, next node will be in a new segment
    upid = curN;
    mcv = MAX_LONG; 
    lastDepMCV = 0; //doesn't matter, will be udpated in the subsequent call
  }

//-logic for joint node
  cType childCnt = pd->gpaccjointid[curN];
  lastJointMCV = min(lastJointMCV,curCV);
  pd->gpaccjointmcv[curN] = lastJointMCV; //记录到最近joint点之前节点的最小cv
  pd->gpaccjointid[curN] = lastJointNodeId;

  assert(pd->gpdep[curN] == 0 || pd->gpaccjointmcv[curN] > 0.1);
  
  //gpaccjointid[curN] is updated by markcut() to contain the number of traversing children
  if(childCnt > 1 ){
    lastJointNodeId = curN;
    lastJointMCV = MAX_LONG;
  }
  else{
    //do nothing
  }


  while (cnt > 0)
  {
    cType zn = pedges->endNode;
    if (pd->gpfa[zn] == curN)
    {
      //此时如果是段尾,mcv应该用cv',每个子是不一样的
      if(upid == curN){
        // assert(mcv == MAX_LONG);
        fcv2 = pd->gpoh[curN];
        if(pd->gpcof[zn] < 0){
          //to keep current child and its tree, father cv2 need to increase a little by -cof_curN
          fcv2 = fcv2 - pd->gpcof[zn];
        }
        mcv = fcv2;
      }

      //TODO:目前这块没有优化，因为后面不太好处理，先运行看结果是否正确；后面再优化
      //这个下面的搜索和上面upid不太一样，情况有点复杂
      // if(lastJointNodeId == curN){
      //   assert(lastJointMCV == MAX_LONG);
      //   fcv2 = pd->gpoh[curN];
      //   if(pd->gpcof[zn] < 0){
      //     //to keep current child and its tree, father cv2 need to increase a little by -cof_curN
      //     fcv2 = fcv2 - pd->gpcof[zn];
      //   }
      //   lastJointMCV = fcv2;
      // }

      buildAcc(pd,zn, upid, mcv,lastDepMCV,lastJointNodeId,lastJointMCV);
    }
    pedges++;
    cnt--;
  }

  // assert(childCnt == 0);
}

void calcuTotalCap(PreprocData *pd)
{
  nodeP *nodes = pd->gd->nodes;

  for (cType curN = 1; curN <= pd->gd->N; curN++)
  {
    nodeP *np = nodes + curN;
    edgeP *pedges = np->edges;
    int cnt = np->nIdx;
    np->totalCap = 0;
    for (int ni = 0; ni < cnt; ni++)
    {
      edgeP *eh = pedges + ni;
      np->totalCap += eh->cap;
    }
  }
}

/*

算法整体步骤：相对之前treem算法的改进
(1)预处理
	//按之前计算，加上一个值放到n上，代表对于n的father,如果去掉n这一支，f的mc变化
	sum_f = 0
	对f的每个为访问的child n:
		在遍历n前，在f上设置oh_f并置0
		在遍历计算中，每次访问祖先，除了计算mc，还更新oh_f (加上就可以)
		n返回后
			此时知道mc_n, oh_f(oh_f就是n这一支连到f的边的值，要包含f_n父子的边)
			这时计算n这一支去掉对f的mc的影响cof_n = oh_f - (mc_n-oh_f) = 2* oh_f - mc_n
				//oh_f是增加的割，mc_n-oh_f是之间到非f的割
			如果cof_n是负值 //说明割值降低了，值得庆贺
				就加到sum_f上,即sum_f 加上 负值，sum_f指的是f的所有减少割值的子n去掉，总共减少的割值
				如果不减少，这个n就不去掉
	//所有child遍历完之后计算mc2_f，就是f的最优的偏特树，此时这个树包含某些子树，而且mc是最小的
	得到mc2_f = mc_f + sum_f 
				
(2)计算时: solve 和 build的时候
	//因为mc2_f是已经去掉cof_n为负值的n的，正值就不管，还在mc_f中
	每次向上回溯，n回溯到f时，如果cof_n是负值，说明如果要保留n这一支，目前f最优割就包含n，即此时f用于计算的mc应该取(mc2_f + -cof_n)，即加上n这一支减掉的值
  现在问题来了：
    f的mc2和访问哪一支有关系，buildAcc预处理咋做？
    这样就意味着，不同的底层上来，每个节点的mc还不一样，导致 节点段 中最小值还不一样
    buildAcc记录的是向上的，所以可以记录的呀

*/

//////////////////////////////////The function to traverse the graph for one pass, i.e. the checkNode function of Algorithm 2 in the paper
void markCut(cType curN, PreprocData *pd)
{
  nodeP* nodes = pd->gd->nodes;
  assert(curN <= pd->gd->N && curN >= 1);

  // printf("******curN is %ld\n",curN);
  assert((nodes + curN)->nIdx > 0);

  short *curS = pd->gps + curN;

  assert(*curS == 0);

  long *curCV = pd->gpcv + curN;
  cType *curDep = pd->gpdep + curN;

  *curS = 1;
  *curCV = 0;
  nodeP *np = nodes + curN;
  edgeP *pedges = np->edges;
  int cnt = np->nIdx;

  if (pedges == NULL)
  {
    *curS = 2;
    return;
  }

  if (np->orderedEdges == NULL)
  {
    np->orderedEdges = (sType *)walloc(cnt + 1, sizeof(sType));
    for (int i = 0; i < cnt; i++)
    {
      np->orderedEdges[i] = i;
    }
  }

  long cap;
  sType *idxs = np->orderedEdges;

  if (pd->mode == 1)
  {
    deOrderEdgeByRandomCap(np,pd); //
  }
  else if (pd->mode == 2)
  {
    aOrderEdgeByAvgCV(np,pd);
  }

  long sum_f = 0;
  for (int ni = 0; ni < cnt; ni++)
  {
    // nodeP* znp = nodes+eh->endNode;

    edgeP *eh = pedges + idxs[ni];
    cType zn = eh->endNode;

    assert(zn != 0);
    assert(zn != curN);

    short zs = pd->gps[zn];

    assert(!(pd->gpfa[zn] == curN && zs == 2));

    // printf("zn is %ld (curN %ld) \n",zn,curN);
    if (zs == 1) // zn is an ancestor node or father node
    {
      // printf("\t zs is 1, zn %ld , *cruCV %ld += %ld\n",zn,*curCV,cap);
      cap = eh->cap;
      *curCV += cap;
      pd->gpcv[zn] -= cap;
      pd->gpoh[zn] += cap;
    }
    else if (zs == 0) // zn is not accessed, i.e., a child node
    {
      //poh临时使用，后面会作为cv2使用：ph记录curN的当前儿子zn子树遍历中，连到curN的边的容量的和，就是直接和curN连接的割值。所以需要置0
      pd->gpoh[curN] = 0;

      pd->gpfa[zn] = curN;
      pd->gpdep[zn] = *curDep + 1;
      pd->gpaccjointid[curN] ++;
      // printf("\t zs is 0, zn %ld , *cruCV %ld before markcut\n",zn, *curCV);
      markCut(zn,pd);
      // printf("----marCut return \n");
      assert(pd->gpdep[zn] == pd->gpdep[curN] + 1);
      // printf("\t zs is %ld , zn %ld , *cruCV %ld += %ld after markcut\n",pd->gps[zn],zn, *curCV,pd->gpcv[zn]);
      *curCV += pd->gpcv[zn];

//       //此时：gpoh[curN]是zn子树连到curN的边总容量，即zn树所有节点脱离curN树后，curN树多出来的割
//         //zn树不连其他curN的子的树，只连curN或上面祖先
//       // pd->gpcv[zn] - pd->gpoh[curN]是zn子树在curN之上的割值, 即zn子树去掉后，curN减少的割值
		 // pd->gpoh[curN] 就是zn子树去掉后，增加的割值
         //cof_zn 就是zn树去掉后，整体增加的割值，如果小于0，就可以去掉
      long cof_zn = pd->gpoh[curN] - ( pd->gpcv[zn] - pd->gpoh[curN]);
      if(cof_zn < 0){ //如果去掉能进一步优化割值(减少)，则记录
        sum_f += cof_zn;
      }
      assert(pd->gpcv[zn] >= pd->gpoh[curN]);
      pd->gpcof[zn] = cof_zn;
      // pd->gpcof[zn] = pd->gpoh[curN];

    }
    else
    {
      //这种情况就是,zn是curN的子树的叶子，正好连到curN有条边
      // printf("zs is %ld\n",zs);
      assert(pd->gpdep[curN] < pd->gpdep[zn]);
      
    }
  }


//下面基于最终确定的curN的cv值做计算
//   
// for (int ni = 0; ni < cnt; ni++)
//   {
//     // nodeP* znp = nodes+eh->endNode;

//     edgeP *eh = pedges + idxs[ni];
//     cType zn = eh->endNode;
//     //此时pd->gpcof[zn]中的值是zn子树遍历完，连接到curN的边的容量的总和
//     if (pd->gpfa[zn] == curN) // zn is not accessed, i.e., a child node
//     {
//       //cof_zn表示zn子树去掉后，对curN树的割值的影响
//       //此时：gpcof[zn]是zn子树连到curN的边总容量，即zn树所有节点脱离curN树后，curN树多出来的割
//         //zn树不连其他curN的子的树，只连curN或上面祖先
//       // pd->gpcv[zn] - gpcof[zn]是zn子树在curN之上的割值,
//       long cof_zn = pd->gpcof[zn] - ( pd->gpcv[curN] - pd->gpcof[zn]);
//       if(cof_zn < 0){
//         sum_f += cof_zn;
//       }      
//       pd->gpcof[zn] = cof_zn;
//     }
//     else
//     {
//       //bypass, no need to handle
//     }
//   }

  //这里是最优cv2的值
  pd->gpoh[curN] = *curCV + sum_f;

  // if(pd->gpoh[curN] < 0){
  //   printf("N %ld\n",curN);
  //   printf("cv %ld\n",pd->gpcv[curN]);
  //   printf("sumf %ld\n",sum_f);
  // }
  if(pd->gpoh[curN] == 0 && curN != gRoot){
    // printf("gpoh = 0 curN is %ld, cv is %ld \n",curN,*curCV);
    assert(1==2);
  }
  if(*curCV == 0 && curN != gRoot){
    // printf("gpoh = 0 curN is %ld, cv is %ld \n",curN,*curCV);
    assert(1==2);
  }

  // assert(pd->gpoh[curN] >0);

  if(pd->mode == 1){
//update ver 2 w,according to
    for (int ni = 0; ni < cnt; ni++)
    {
      // nodeP* znp = nodes+eh->endNode;

      edgeP *eh = pedges + idxs[ni];
      cType zn = eh->endNode;
      // nodeP *znp = nodes+zn;

      assert(zn != 0);
      assert(zn != curN);
      short zs = pd->gps[zn];
    

      //progate weight to curN's edges
      if (zs == 1 && pd->gpdep[zn] != *curDep - 1)
      {
          cType weight = eh-> w;
          if(eh->avgCV == 0){
            eh->avgCV = MAX_LONG;
          }
          eh->avgCV = min(eh->avgCV, *curCV);//((eh->avgCV) * weight + *curCV)/(weight+1);
          eh->w = weight+1;
          
          edgeP *reh = eh->rev;

          if(reh->avgCV == 0){
            reh->avgCV = MAX_LONG;
          }

          weight = reh-> w;
          reh->avgCV = min(reh->avgCV, *curCV);//((reh->avgCV) * weight + *curCV)/(weight+1);
          reh->w = weight+1;

      }
      
    }
  }

    
  assert(pd->gpdep[curN] == 0 || *curCV >0);

  // printf("set curN %ld to stat 2 \n",curN);
  *curS = 2;

}

////////////////////////////////The function to obtain min-cut value of given node pair, i.e., Algorithm 3 in the paper
/*
 (2)求解时：
      深度大的出发节点直接cv2，
      另外一个不是这个的祖先时，另外一个也可以用cv2
      [这个先不优化有点复杂]如果t是s祖先，
        如果cv2正好割掉下面，直接可以用cv2
        如果不是，也可以计算割掉对应树后这个t的割

      PS: t是s祖先，可以用cv2,t不是s的祖先也可以cv2，两个cv2都可以用
      问题是，如果t是s祖先，t的cv2对应的割并不能切断s这条支线，这样就不对了
        如果t是s祖先，其实我们算的是去掉这个支后的t的最小割
      那就简化：
        只要t不是s祖先，就可以用t的cv2

      后面的逐个逼近，需要用cv'
      
*/
long solveMaxFlowAccVER4(long minCandi, NodePropArr np, cType s, cType t, int SPAN_LEN)
{
  cType *pDep = np.pdep;
  long *pCV = np.pcv;
  long *poh = np.poh;
  long *pcof = np.pcof;
  cType *pFa = np.pfa;
  cType *paccup = np.pacc_upid;
  long *paccmcv = np.pacc_upmincv;
  cType *paccposmcv = np.pacc_pos_upmincv;
  cType *jup = np.pacc_jointid;
  long *jmcv = np.pacc_jointmcv;

  // printf("*********sovelstart\n");
  //先调换保证pDep[s]>=pDep[t]
  assert(s != t);
  if (pDep[s] < pDep[t])
  {
    cType tmp = s;
    s = t;
    t = tmp;
  }

  // cType ot = t;
  cType depT = pDep[t];
  assert(pDep[s] >= depT);

  long mcv = MAX_LONG;
  //先把s,t的cv2考虑进去
  mcv = poh[s]; //相当于上面出发点直接cv2, t不确定，如果包含s就不能用他的cv2

  cType ups = paccup[s]; //找到上一个段尾
  //注意：我们需要找到s到up的mcv被纳入计算，但实际up或更多下面节点的cv'不能作为候选割

  while (pDep[ups] > depT) //   如果pDep[ups] == depT，就不会继续，pDep[ups] > depT，此时ups的cv'肯定是纳入计算的，没问题
  {
    assert(pDep[ups] % SPAN_LEN == 0);
    mcv = min(mcv, paccmcv[s]); //paccmcv可以包含上个段尾的cv', 因为到这里是pDep[ups]>depT成立，肯定包含ups这个段尾的cv'
    s = ups;
    ups = paccup[ups];
  } 

 

//   assert(mcv >100.0);
  assert(pDep[ups] <=depT && pDep[s] >= depT);

  cType upt = t;

  if (pDep[t] % SPAN_LEN != 0)
  {
    upt = paccup[t];
  }

  assert(pDep[ups] == pDep[upt]); //s和t的up到达同一个深度，此时t还在原地(t本身可能就是up)
  if(ups != upt){
  //如果ups != upt, 肯定可以确认t不是s祖先，可以用t的cv2
    mcv = min (mcv, poh[t]);
  }
  else{
    //有可能s是t的祖先，也可能分叉，我们就不考虑了
  }

  while (ups != upt) //只要ups!=upt，则ups和upt的cv'都可以分开s和t，都是候选
  {
    mcv = min(mcv, min(paccmcv[s], paccmcv[t])); //ups != upt， 则段尾的cv'可以包含

    s = ups;
    ups = paccup[ups];

    t = upt;
    upt = paccup[upt];

    assert(pDep[s] % SPAN_LEN == 0);
    assert(pDep[t] == pDep[s]);
  }        
  
  assert(ups == upt);//找到共同的根

  // int maybeTisAncestorofS = 0;
  // if(t == ot){
  //   //如果upt没挪过，ups肯定也没挪过，等于直接s上回溯到t附近，而且up是同一个 
  //   //PS: t如果挪过肯定不是s的祖先了  
  //   //此时可能t不是s祖先，只是t的up是s的祖先，所以不能判断
  //   //即要从最近分叉t和祖先t两种情况做区分
  //   maybeTisAncestorofS = 1;
  // }

  // printf("s1: mcv is %ld\n",mcv);

  if(s == t){ 
    //t是s的祖先,且s回溯正好到t,说明t正好割掉下面，取t的cv2作为一个候选
    // mcv = min (mcv, poh[t]);
    return mcv;
  }
  
  cType min_bound2 = min(paccmcv[s],paccmcv[t]); //注意：这个只是判断是否有必要向上再找了，没必要直接返回mcv, cv'也没问题

  if(min_bound2 >= mcv || min_bound2 >= minCandi){
    //no need to search
    return mcv;
  }

  if(min_bound2 == paccmcv[s] && pDep[t]+paccposmcv[s] < pDep[s]){
    return mcv;
  }

// printf("s2: mcv is %ld, min_bound2 is %ld\n",mcv,min_bound2);

  //下面说明，可能有必要再找更小的mcv

  ///////////////////////check inside one SPAN
  //(1) we need to check whether s and t in the same line, i.e., t is the ancestor of s  
  //the only way is to approach the depth of t and check

  if(pDep[s] != pDep[t]){

    if(pDep[s] < pDep[t]){
      cType tmp = s;
      s = t;
      t = tmp;
    }  

    cType jups = jup[s];
    cType depT = pDep[t];
    while(pDep[jups] > depT){ //pDep[jups]  >depT，jups的cv'是候选
      mcv = min(mcv, jmcv[s]);
      if(mcv == min_bound2){
        return mcv;
      }

      s = jups;
      jups = jup[s];

    }

  // printf("\ts3: mcv is %ld\n",mcv);
    //下面的讨论简历在jmcv使用cv'优化的基础上
    /*
      cv'不是包含谁时的cv，而是如果包含的这支cof是负，即这支去掉实际增加的割是负值，即实际能减少割，则把加回来；而如果这支去掉能增加割值，实际保留这支就是cv2,
    */

   //目前这块不受cv2 cv'的影响
    if(pDep[jups] == depT){ 
      if(jups == t){
        mcv = min(mcv,jmcv[s]); //此时jmcv[s]是t包含这个分支的割，去掉这个分支实际结果如果增加的是负值，那就在cv2中；如果去掉增加的是正值，cv2肯定包含这条分支，cv2不能分割，如果分割只能去掉，则实际值比cv2要大。此时cv'实际
        //cv2可能是候选值(如果不包含这个分支)，也可能不是(包含这个分支),此时jmcv也不对了，比实际选项可能小，因为包含这个分支存在的情况
        // mcv = min(mcv, poh[t]); //t的cv2是一个候选值，因为也可以分隔。t不一定是之前的t了，如果不是t就是共同祖先,t的cv2
        // printf("hhhere return %ld\n",mcv);
        return mcv; // jmcv[s]包含有jups的cv',也就是t到s这一支时包含s时t的cv'，那就不是能分割s和t的候选，必须要把s这一支切掉；也就是说如果t去掉s后，实际割变大了，这个结果有可能就不对。不对但是实际上只可能比cv2大,直接考虑t的cv2即可
      }
      else{
        //s and t in two lines
        assert(pDep[jups] == depT && pDep[s] > depT);
        goto STEP_CHECK_IN_TWOLINES;
      }
    }
    else{
      assert(pDep[jups] < depT && pDep[s] > depT);
      cType os = 0;
      long nCV = MAX_LONG;
      while(pDep[s] > depT){
        if(os != 0){
          nCV = poh[s];
          if(pcof[os] < 0){
            // s的cv2不包含os，因为os的cof负值，即去掉使得s的更小
            nCV = nCV - pcof[os];
          }
          assert(nCV <= pCV[s]);
        }
        
        mcv = min(mcv,nCV);

        if(mcv == min_bound2){
          return mcv;
        }
        os = s;
        s = pFa[s];        
      }

      if(s == t){
        return mcv;
      }

      assert(s!=t && pDep[s] == depT);
      //s and t in two lines.
      goto STEP_CHECK_IN_TWOLINES;

    }
  }
  else{
      //pDep[s] == pDep[t];
      if(s == t){
        return mcv;
      }    
      goto STEP_CHECK_IN_TWOLINES;
  }
  // printf("\t\ts3: mcv is %ld\n",mcv);
STEP_CHECK_IN_TWOLINES:

  while (s != t)
  { 
    // assert(jmcv[s] > 0.1);
    // assert(jmcv[t] > 0.1);
    if(pDep[s] > pDep[t]){
      mcv = min(mcv, jmcv[s]);
      if(mcv == min_bound2){
        return mcv;
      }      
      s = jup[s];
    }
    else if(pDep[s] < pDep[t]){
      mcv = min(mcv, jmcv[t]);
      if(mcv == min_bound2){
        return mcv;
      }      
      t = jup[t];
    }
    else{
      mcv = min(mcv, min(jmcv[s],jmcv[t]));
      if(mcv == min_bound2){
        return mcv;
      }         
      s = jup[s];
      t = jup[t];
    }

  }

  return mcv;

}

//////////////////////function to load graph data
void loadGraphData(PreprocData *pd){
  pd->gd = walloc(1,sizeof(GraphData));  
  printf("c\nc hi_treem version 0.9\n");
  printf("c Copyright C by nsyncw, nsyncw@gmail.com\nc\n");

  parse(&(pd->gd->N), &(pd->gd->M), &(pd->gd->nodes));

  printf("c nodes:       %10ld\nc arcs:        %10ld\nc\n", pd->gd->N, pd->gd->M);
}

///////////////////function to initialize data structure
void initPreprocData(PreprocData *pd){
  pd->rd = NULL;
  pd->SPAN_LEN = (int)(sqrt(pd->gd->N));

  pd->roots = (cType *)walloc(pd->total + 2, sizeof(cType));
  pd->allResults = walloc(pd->total+2, sizeof(NodePropArr));

  NodePropArr * allResults = pd->allResults;
  cType len = pd->gd->N + 2;

  calcuTotalCap(pd);

  for (int i = 0; i < pd->total; i++)
  {
    allResults[i].pfa = (cType *)walloc(len, sizeof(cType));
    allResults[i].pdep = (cType *)walloc(len, sizeof(cType));
    allResults[i].pcv = (long *)walloc(len, sizeof(long));
    allResults[i].poh = (long *)walloc(len, sizeof(long));
    allResults[i].pcof = (long *)walloc(len, sizeof(long));
    allResults[i].ps = (short *)walloc(len, sizeof(short));
    allResults[i].pacc_upid = (cType *)walloc(len, sizeof(cType));
    allResults[i].pacc_upmincv = (long *)walloc(len, sizeof(long));
    allResults[i].pacc_pos_upmincv = (cType *)walloc(len, sizeof(cType));
    allResults[i].pacc_jointid = (cType *)walloc(len, sizeof(cType));
    allResults[i].pacc_jointmcv = (long *)walloc(len, sizeof(long));

    memset(allResults[i].pfa, 0, len * sizeof(cType));
    memset(allResults[i].pdep, 0, len * sizeof(cType));
    memset(allResults[i].pcv, 0, len * sizeof(long));
    memset(allResults[i].poh, 0, len * sizeof(long));
    memset(allResults[i].pcof, 0, len * sizeof(long));
    memset(allResults[i].ps, 0, len * sizeof(short));
    memset(allResults[i].pacc_upid, 0, len * sizeof(cType));
    memset(allResults[i].pacc_upmincv, 0, len * sizeof(long));
    memset(allResults[i].pacc_pos_upmincv, 0, len * sizeof(cType));
    memset(allResults[i].pacc_jointid, 0, len * sizeof(cType));
    memset(allResults[i].pacc_jointmcv, 0, len * sizeof(long));
  }  
}


/////////////////////function to traverse the graph data for multiple times, i.e., Algorithm 2 in the paper
void preProc(PreprocData *pd){
  double tm;
  double totalProcTime = 0;
  NodePropArr *allResults = pd->allResults;
  //calculate total cap of one node
  cType root;
  for (int ipass = 0; ipass < pd->total; ipass++)
  {
    if(pd->rd != NULL){
      free(pd->rd);
      pd->rd = NULL;
    }
    pd->rd = initrand(pd->gd->M*2);    
    // printf("the %d times\n",i);
    pd->gpfa = allResults[ipass].pfa;
    pd->gpdep = allResults[ipass].pdep;
    pd->gpcv = allResults[ipass].pcv;
    pd->gpoh = allResults[ipass].poh;
    pd->gpcof = allResults[ipass].pcof;
    pd->gps = allResults[ipass].ps;
    pd->gpaccup = allResults[ipass].pacc_upid;
    pd->gpaccmcv = allResults[ipass].pacc_upmincv;
    pd->gpaccposmcv = allResults[ipass].pacc_pos_upmincv;
    pd->gpaccjointid = allResults[ipass].pacc_jointid;
    pd->gpaccjointmcv = allResults[ipass].pacc_jointmcv;

    pd->mode = ipass < pd->P * pd->total / 100 ? 1 : 2;
    
    root = 1 + ((mrand(pd->rd) * mrand(pd->rd)) % pd->gd->N);

    pd->roots[ipass] = root;
    pd->gpdep[root] = 0;
    printf("pass %d before markCut: root is %ld\n",ipass,root);
    fflush(stdout);
    //printf("pass %d, randidx %ld, root is %ld\n",i, randNumIdx,root);
    // printf("root fa %ld\n",allResults[i].pfa[root]);
    tm = timer();
    gRoot = root;
    
    markCut(root,pd);
    pd->gpcv[root] = MAX_LONG;
    pd->gpoh[root] = MAX_LONG;

    printf("c before buildAcc\n");
	fflush(stdout);
    buildAcc(pd, root, root, MAX_LONG, pd->gpdep[root],root,MAX_LONG);
    printf("c after buildAcc\n");
    fflush(stdout);


    totalProcTime += timer() - tm;
    printf("c proctime for onepass: %10.06f\n", timer() - tm);
    if (ipass % 10 == 0)
    {
      printf("c the %d passes\n", ipass);
    }
  }

  printf("c preprocess times %10.6f\n", totalProcTime);

}


//////////////////////////function to calculate multiple random node pairs, i.e., the calling of Algoirthm 3 for multiple times
void calcuRandomPairs(int numOfPairs, PreprocData *pd){
  double totalTime = 0;
  long mv = MAX_LONG;

  double curTime = 0;
  cType ns, nt;

  if(pd->rd != NULL){
    free(pd->rd);
    pd->rd = NULL;
  }
  pd->rd = initrand(pd->gd->M*2);  

  for (int ipair = 0; ipair < numOfPairs;)
  {

    // printf("%d\n",i);
    ns = 1 + ((mrand(pd->rd) * mrand(pd->rd)) % (pd->gd->N));
    nt = 1 + ((mrand(pd->rd) * mrand(pd->rd)) % (pd->gd->N));
    if (ns != nt)
    {
      // mv = MAX_LONG;
      mv = min((pd->gd->nodes+ns)->totalCap, (pd->gd->nodes+nt)->totalCap);
      
      curTime = timer();
      for (int j = 0; j < pd->total; j++)
      {
        long tmp = solveMaxFlowAccVER4(mv, pd->allResults[j], ns, nt,pd->SPAN_LEN);
        // printf("--solve return %ld\n",tmp);
        if (mv > tmp)
        {
          mv = tmp;
        }
        // printf("--mv is %ld\n",mv);
      }
      curTime = timer() - curTime;
      totalTime += curTime;
      ipair++;
      printf("c hi_treem_res(n,s,mflow,tm) %lu %lu %12.01f %12.06f1\n", ns, nt, 1.0 * mv, curTime);
    }
  }

  printf("c run ok! average time %10.6f\n", totalTime / numOfPairs);


}


