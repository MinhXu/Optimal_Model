import java.util.ArrayList;

import gurobi.*;

public class Callback1 extends GRBCallback {
  private double     lastiter;
  private double     lastnode;
  private GRBVar[]   yvars;
  private double[] yvalues;
  private int d;
  private int n;
  private int m;
  private int[][] w;
  private int[] b_d;
  private int counterLimit;
  private int counter;
  private GRBVar[]   xvars;
  private double[] xvalues;
  //private FileWriter logfile;

  public Callback1(GRBVar[] _xvars,GRBVar[] _yvars,int _d,int _n,int _m,int[][] _w,int[] _b,int _counterLimit) {
    lastiter = lastnode = -GRB.INFINITY;
    yvars = _yvars;
    xvars = _xvars;
    d=_d;
    n=_n;
    m=_m;
    w=_w;
    b_d = _b;
    counterLimit = _counterLimit;
    
    //logfile = xlogfile;
  }
  
   
	public void combinations(int noComb, ArrayList<Integer> arr, ArrayList<Integer> list,int startPoisition,ArrayList<ArrayList<Integer>> result) {
		
		
		if(list.size()<=0)
		{
			for (int i=0;i<noComb;i++)
				list.add(-1);
		}		
		if (noComb == 0){
			ArrayList<Integer> t= new ArrayList<>();
			for(int i=0;i<list.size();i++)
				t.add(list.get(i));
	          result.add(t);
	          list = new ArrayList<>();
	          return;
	      } 
		
	      for (int i = startPoisition; i <= arr.size()-noComb; i++){
	          list.set(list.size() - noComb,arr.get(i));
	          combinations(noComb-1,arr, list, i+1,result);
	      }
	    }
	
  public ArrayList<ArrayList<Integer>> FindCover(ArrayList<Integer> idSet, int[] b_d,int _w, int noCover)
  {
	  ArrayList<ArrayList<Integer>> temp = new ArrayList<>();
	  ArrayList<ArrayList<Integer>> comb = new ArrayList<>();
	  ArrayList<Integer> combLst = new ArrayList<>();
	  combinations(noCover, idSet, combLst,0,comb);
	  for(int i=0;i<comb.size();i++)
	  {
		  ArrayList<Integer> cover1= comb.get(i);
		  double sum=0;
		  for(int j=0;j<cover1.size();j++)
			  sum+= b_d[cover1.get(j)];
		  if(sum>_w)
			  temp.add(cover1);
	  }
	  return temp;
  }
  
  protected void callback()
  {

	    try {
	    	if (where == GRB.CB_MIPNODE) {
	            // MIP node callback
	          
	            if (getIntInfo(GRB.CB_MIPNODE_STATUS) == GRB.OPTIMAL  ) {
	            	
	            	System.out.println("aaa+ "+counter);
	            	if(counter<counterLimit)
	            	{
	            		double eps = 0.01;
		            	yvalues= getNodeRel(yvars);
		            	for(int i=0;i<yvalues.length;i++)
		            	{
		            		if(yvalues[i]!=0.0 && yvalues[i]!=1.0)
		            		{
		            			if(yvalues[i]<=eps)
		            				setSolution(yvars[i], 0.0);
		            			if(yvalues[i]>= 1.0-eps)
		            				setSolution(yvars[i], 1.0);
		            		}
		            	}
		            	xvalues= getNodeRel(xvars);
		            	for(int i=0;i<xvalues.length;i++)
		            	{
		            		if(xvalues[i]!=0.0 && xvalues[i]!=1.0)
		            		{
		            			if(xvalues[i]<=eps)
		            				setSolution(xvars[i], 0.0);
		            			if(xvalues[i]>= 1.0-eps)
		            				setSolution(xvars[i], 1.0);
		            		}
		            	}
	            	}
	            	counter++;
	        // MIP solution callback -> flow cover
	            	
	            	

	      }
	      }
	    } catch (GRBException e) {
	      System.out.println("Error code: " + e.getErrorCode());
	      System.out.println(e.getMessage());
	      e.printStackTrace();
	    } catch (Exception e) {
	      System.out.println("Error during callback");
	      e.printStackTrace();
	    }
	  

  }

  protected int[] sortDecreasing(double[] srcLst)
  {

	  int[] temp= new int[srcLst.length];
		int dem=0;
		double[] savelst = new double[srcLst.length];
		for(int i=0;i<srcLst.length;i++)
			savelst[i]=srcLst[i];
		
		while (dem<srcLst.length)
		{
			double max=-1.0;
			int id=-1;
			for (int i=0;i< srcLst.length;i++)
			{
				double dtemp= srcLst[i];
				if(dtemp>max && dtemp!=-1)
				{
					max = dtemp;
					id=i;
				}
			
			}			
			if(id==-1)
			{
				System.out.println("Het chua 1 "+ dem);
				return null;
			}
			srcLst[id] = -1.0;
			temp[dem]=id;
			dem++;
		}
		return temp;
	
	  
  
  }
  protected int[] sortVal(ArrayList<Double> srcLst1)
  {
	  double[] srcLst = new double[srcLst1.size()];
	  for(int i=0;i<srcLst1.size();i++)
		  srcLst[i]= srcLst1.get(i);
	  int[] temp= new int[srcLst.length];
		int dem=0;
		
		while (dem<srcLst.length)
		{
			double min=10000.0;
			int id=-1;
			for (int i=0;i< srcLst.length;i++)
			{
				double dtemp= srcLst[i];
				if(dtemp<min)
				{
					min = dtemp;
					id=i;
				}
			
			}			
			if(id==-1)
			{
				System.out.println("Het chua "+ dem);
				continue;
			}
			srcLst[id] =100000.0;
			temp[dem]=id;
			dem++;
		}
		return temp;
	
	  
  }
  protected double[] getVar()
  {
	  return yvalues;
  }
  protected void callbackChuan() {
    try {
      if (where == GRB.CB_POLLING) {
        // Ignore polling callback
      } else if (where == GRB.CB_PRESOLVE) {
        // Presolve callback
        int cdels = getIntInfo(GRB.CB_PRE_COLDEL);
        int rdels = getIntInfo(GRB.CB_PRE_ROWDEL);
        
//        values       = getSolution(vars);
//        double[][][] valY= new double[d][n][n];
//
//        for (int i=0;i<values.length;i++)
//        {
//        	int k= i%d;
//    		int temp = i/d;
//    		int j1= temp/n;
//    		int j2= temp%n;
//    		valY[k][j1][j2]=values[i];
//        	if(values[i]>0)
//        	{
//        		
//        		System.out.println("d["+i+1+"]="+values[i] +":"+valY[k][j1][j2]);
//        	}
//        }
        if (cdels != 0 || rdels != 0) {
          System.out.println(cdels + " columns and " + rdels
              + " rows are removed");
        }
      } else if (where == GRB.CB_SIMPLEX) {
        // Simplex callback
        double itcnt = getDoubleInfo(GRB.CB_SPX_ITRCNT);
        if (itcnt - lastiter >= 100) {
          lastiter = itcnt;
          double obj    = getDoubleInfo(GRB.CB_SPX_OBJVAL);
          int    ispert = getIntInfo(GRB.CB_SPX_ISPERT);
          double pinf   = getDoubleInfo(GRB.CB_SPX_PRIMINF);
          double dinf   = getDoubleInfo(GRB.CB_SPX_DUALINF);
          char ch;
          if (ispert == 0)      ch = ' ';
          else if (ispert == 1) ch = 'S';
          else                  ch = 'P';
          System.out.println(itcnt + " " + obj + ch + " "
              + pinf + " " + dinf);
        }
      } else if (where == GRB.CB_MIP) {
        // General MIP callback
        double nodecnt = getDoubleInfo(GRB.CB_MIP_NODCNT);
        double objbst  = getDoubleInfo(GRB.CB_MIP_OBJBST);
        double objbnd  = getDoubleInfo(GRB.CB_MIP_OBJBND);
        int    solcnt  = getIntInfo(GRB.CB_MIP_SOLCNT);
        if (nodecnt - lastnode >= 100) {
          lastnode = nodecnt;
          int actnodes = (int) getDoubleInfo(GRB.CB_MIP_NODLFT);
          int itcnt    = (int) getDoubleInfo(GRB.CB_MIP_ITRCNT);
          int cutcnt   = getIntInfo(GRB.CB_MIP_CUTCNT);
          System.out.println(nodecnt + " " + actnodes + " "
              + itcnt + " " + objbst + " " + objbnd + " "
              + solcnt + " " + cutcnt);
        }
        if (Math.abs(objbst - objbnd) < 0.1 * (1.0 + Math.abs(objbst))) {
          System.out.println("Stop early - 10% gap achieved");
          abort();
        }
        if (nodecnt >= 10000 && solcnt > 0) {
          System.out.println("Stop early - 10000 nodes explored");
          abort();
        }
      } else if (where == GRB.CB_MIPSOL) {
        // MIP solution callback
        int      nodecnt = (int) getDoubleInfo(GRB.CB_MIPSOL_NODCNT);
        double   obj     = getDoubleInfo(GRB.CB_MIPSOL_OBJ);
        int      solcnt  = getIntInfo(GRB.CB_MIPSOL_SOLCNT);
        double[] x       = getSolution(yvars);
        System.out.println("**** New solution at node " + nodecnt
            + ", obj " + obj + ", sol " + solcnt
            + ", x[0] = " + x[0] + " ****");
      } else if (where == GRB.CB_MIPNODE) {
        // MIP node callback
        System.out.println("**** New node ****");
        if (getIntInfo(GRB.CB_MIPNODE_STATUS) == GRB.OPTIMAL) {
          //double[] x = getNodeRel(vars);
          //setSolution(vars, x);
        	
        	System.out.println("Co len co len");
          yvalues= getNodeRel(yvars);
          double[][][] valY= new double[d][n][n];
	        
	        for (int i=0;i<yvalues.length;i++)
	        {
	        	int k= i%d;
    		int temp = i/d;
    		int j1= temp/n;
    		int j2= temp%n;
    		valY[k][j1][j2]=yvalues[i];
	        	if(yvalues[i]>0)
	        	{
	        		
	        		System.out.println("d["+i+1+"]="+yvalues[i] +":"+valY[k][j1][j2]);
	        	}
	        }
          
        }
      } else if (where == GRB.CB_BARRIER) {
        // Barrier callback
        int    itcnt   = getIntInfo(GRB.CB_BARRIER_ITRCNT);
        double primobj = getDoubleInfo(GRB.CB_BARRIER_PRIMOBJ);
        double dualobj = getDoubleInfo(GRB.CB_BARRIER_DUALOBJ);
        double priminf = getDoubleInfo(GRB.CB_BARRIER_PRIMINF);
        double dualinf = getDoubleInfo(GRB.CB_BARRIER_DUALINF);
        double cmpl    = getDoubleInfo(GRB.CB_BARRIER_COMPL);
        System.out.println(itcnt + " " + primobj + " " + dualobj + " "
            + priminf + " " + dualinf + " " + cmpl);
      } else if (where == GRB.CB_MESSAGE) {
        // Message callback
        //String msg = getStringInfo(GRB.CB_MSG_STRING);
        //if (msg != null) logfile.write(msg);
      }
    } catch (GRBException e) {
      System.out.println("Error code: " + e.getErrorCode());
      System.out.println(e.getMessage());
      e.printStackTrace();
    } catch (Exception e) {
      System.out.println("Error during callback");
      e.printStackTrace();
    }
  }
}