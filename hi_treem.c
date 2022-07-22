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
///////////////////////////////////////// The definition of graph data structure
/////////////////////////////////////////

//data structure that holds graph data
typedef
struct GraphData_{

  long N, M; //The number of nodes and edges in the graph
  nodeP *nodes;  // The node array, each is the info of one node and all its edges to the nodes with bigger ID than it

} GraphData;

//data structure that holds data for randomrization, thus can be quickly fetched in the process.
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

  //holds the resulting data in all passes
  NodePropArr* allResults;

  //pre-generated auxiliary data
  RandomData* rd;

  //<BEING> hold the hot data in current pass
  cType *gpfa; // [i] is the father id of node i
  cType *gpdep; // [i] is the traversal depth of node i
  long *gpcv; // [i] is the cv of node i
  long *gpoh; //[i] is the cv~ of node i
  long *gpcof; //[i] is the pv of node i
  short *gps; // [i] is the state of node i
  cType *gpaccup; //[i] is the sh of node i in Algorithm 3
  long *gpaccmcv; //[i] is mcv of node i  in Algorithm 3
  cType *gpaccposmcv; // some small improvement to Algorithm 3, not affecting the declared performance in the paper
  cType *gpaccjointid;   // not used in solving 
  long *gpaccjointmcv; // not used in solving 
  //<END>

  cType *roots; //records root in each pass

  int mode; //the traversing mode, as explained in the paper

  int P; // P% percent of total passes in mode 1, the remaining in mode 2
  int total; //number of total passes
  int SPAN_LEN; //the length of a ancestor span, used for acceleration in traversal trees

} PreprocData;




///////////////////////////////////////////
///////////////////////////////////////////The auxiliary functions
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

/////////////////////////The two function for heap sorting edges, used in Algorithm 2 to order the edges of a node  
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
  the Algorithm 3 in the paper
  the function to add more data to a traversal tree to accelerate the searching in the tree
  The idea is to precalcuate minimal cv value of a span of nodes in a traversal tree, e.g., when SPAN_LEN = 100, and a node has depth of 200, then the algorithm will pre-calculate the minimal cv value of the nodes between the node (dep=200) and an acestor(dep=101)
  upid is the id of the last SPAN node, mcv is the min cv among all previous nodes in the recent SPAN
  lastDepMCV is the depth of the node depth that has the minimal cv in the span
  lastJointNodeId is the last ancestor node id that has more than one child nodes
  lastJointMCV is the cv of lastJoineNodeId
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

//-logic for joint node, not used in solving
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

      if(upid == curN){
        // assert(mcv == MAX_LONG);
        fcv2 = pd->gpoh[curN];
        if(pd->gpcof[zn] < 0){
          //to keep current child and its tree, father cv2 need to increase a little by -cof_curN
          fcv2 = fcv2 - pd->gpcof[zn];
        }
        mcv = fcv2;
      }

      buildAcc(pd,zn, upid, mcv,lastDepMCV,lastJointNodeId,lastJointMCV);
    }
    pedges++;
    cnt--;
  }

}

//calculate the total capacity of  each node
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

//////////////////////////////////The function to traverse the graph for one pass, i.e. the CheckNode function of Algorithm 2 in the paper
void markCut(cType curN, PreprocData *pd)
{
  nodeP* nodes = pd->gd->nodes;
  assert(curN <= pd->gd->N && curN >= 1);

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

    edgeP *eh = pedges + idxs[ni];
    cType zn = eh->endNode;

    assert(zn != 0);
    assert(zn != curN);

    short zs = pd->gps[zn];

    assert(!(pd->gpfa[zn] == curN && zs == 2));


    if (zs == 1) // zn is an ancestor node or father node
    {

      cap = eh->cap;
      *curCV += cap;
      pd->gpcv[zn] -= cap;
      pd->gpoh[zn] += cap;
    }
    else if (zs == 0) // zn is not accessed, i.e., a child node
    {
     pd->gpoh[curN] = 0;

      pd->gpfa[zn] = curN;
      pd->gpdep[zn] = *curDep + 1;
      pd->gpaccjointid[curN] ++;

      markCut(zn,pd);

      assert(pd->gpdep[zn] == pd->gpdep[curN] + 1);

      *curCV += pd->gpcv[zn];


      long cof_zn = pd->gpoh[curN] - ( pd->gpcv[zn] - pd->gpoh[curN]);
      if(cof_zn < 0){ 
        sum_f += cof_zn;
      }
      assert(pd->gpcv[zn] >= pd->gpoh[curN]);
      pd->gpcof[zn] = cof_zn;

    }
    else
    {

      assert(pd->gpdep[curN] < pd->gpdep[zn]);
      
    }
  }




   pd->gpoh[curN] = *curCV + sum_f;


  if(pd->gpoh[curN] == 0 && curN != gRoot){
   
    assert(1==2);
  }
  if(*curCV == 0 && curN != gRoot){
    
    assert(1==2);
  }



  if(pd->mode == 1){

    for (int ni = 0; ni < cnt; ni++)
    {


      edgeP *eh = pedges + idxs[ni];
      cType zn = eh->endNode;


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


  *curS = 2;

}

////////////////////////////////The function to obtain min-cut value of given node pair, i.e., Algorithm 3 in the paper
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


  assert(s != t);
  if (pDep[s] < pDep[t])
  {
    cType tmp = s;
    s = t;
    t = tmp;
  }


  cType depT = pDep[t];
  assert(pDep[s] >= depT);

  long mcv = MAX_LONG;

  mcv = poh[s]; //相当于上面出发点直接cv2, t不确定，如果包含s就不能用他的cv2

  cType ups = paccup[s]; //找到上一个段尾


  while (pDep[ups] > depT) //   如果pDep[ups] == depT，就不会继续，pDep[ups] > depT，此时ups的cv'肯定是纳入计算的，没问题
  {
    assert(pDep[ups] % SPAN_LEN == 0);
    mcv = min(mcv, paccmcv[s]); //paccmcv可以包含上个段尾的cv', 因为到这里是pDep[ups]>depT成立，肯定包含ups这个段尾的cv'
    s = ups;
    ups = paccup[ups];
  } 

 


  assert(pDep[ups] <=depT && pDep[s] >= depT);

  cType upt = t;

  if (pDep[t] % SPAN_LEN != 0)
  {
    upt = paccup[t];
  }

  assert(pDep[ups] == pDep[upt]); 
  if(ups != upt){

    mcv = min (mcv, poh[t]);
  }
  else{
    //do nothing
  }

  while (ups != upt) 
  {
    mcv = min(mcv, min(paccmcv[s], paccmcv[t])); 

    s = ups;
    ups = paccup[ups];

    t = upt;
    upt = paccup[upt];

    assert(pDep[s] % SPAN_LEN == 0);
    assert(pDep[t] == pDep[s]);
  }        
  
  assert(ups == upt);//找到共同的根




  if(s == t){ 
    return mcv;
  }
  
  cType min_bound2 = min(paccmcv[s],paccmcv[t]); 

  if(min_bound2 >= mcv || min_bound2 >= minCandi){
    //no need to search
    return mcv;
  }

  if(min_bound2 == paccmcv[s] && pDep[t]+paccposmcv[s] < pDep[s]){
    return mcv;
  }





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


    if(pDep[jups] == depT){ 
      if(jups == t){
        mcv = min(mcv,jmcv[s]); 
        return mcv; 
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
      
      if(s == t){
        return mcv;
      }    
      goto STEP_CHECK_IN_TWOLINES;
  }

STEP_CHECK_IN_TWOLINES:

  while (s != t)
  { 

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
  cType root;
  for (int ipass = 0; ipass < pd->total; ipass++)
  {
    if(pd->rd != NULL){
      free(pd->rd);
      pd->rd = NULL;
    }
    pd->rd = initrand(pd->gd->M*2);    
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


    ns = 1 + ((mrand(pd->rd) * mrand(pd->rd)) % (pd->gd->N));
    nt = 1 + ((mrand(pd->rd) * mrand(pd->rd)) % (pd->gd->N));
    if (ns != nt)
    {

      mv = min((pd->gd->nodes+ns)->totalCap, (pd->gd->nodes+nt)->totalCap);
      
      curTime = timer();
      for (int j = 0; j < pd->total; j++)
      {
        long tmp = solveMaxFlowAccVER4(mv, pd->allResults[j], ns, nt,pd->SPAN_LEN);
        
        if (mv > tmp)
        {
          mv = tmp;
        }

      }
      curTime = timer() - curTime;
      totalTime += curTime;
      ipair++;
      printf("c hi_treem_res(n,s,mflow,tm) %lu %lu %12.01f %12.06f1\n", ns, nt, 1.0 * mv, curTime);
    }
  }

  printf("c run ok! average time %10.6f\n", totalTime / numOfPairs);


}


