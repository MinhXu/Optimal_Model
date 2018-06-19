import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.Vector;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.*;

import org.apache.commons.io.FileUtils;

import gurobi.*;
import gurobi.GRB.IntParam;

import org.jgrapht.DirectedGraph;
import org.jgrapht.GraphPath;
import org.jgrapht.alg.*;
import org.jgrapht.graph.*;
import org.uncommons.maths.random.ExponentialGenerator;
import org.uncommons.maths.random.PoissonGenerator;

import com.sun.xml.internal.bind.v2.runtime.unmarshaller.XsiNilLoader.Array;

import ilog.concert.*;
import ilog.cplex.*;

public class Main {
	static BufferedWriter out;
	static BufferedReader in;
	static int c,n,m,d,z,E,_no,noOldDemand;
	static MyGraph g;
	static Function[] functionArr;
//	static Demand[] demandArr;
	static ArrayList<Demand> demandArray;
	static GRBVar[][][]x1;//function on node
	static GRBVar[][][] y1;//link 
	static GRBVar[][][][] phi;
	static GRBVar[] m_y,blocking;
	static GRBVar r_l,r_n,r;
	static long _duration=0;
	static double value_final=0.0;
	static double value_bandwidth=0.0;
	static double ultilize_resource =0.0;
	static double currentTime=0.0;
	static double maxNode =0;
	static int prevNode;
	static double maxNodeLoad =0;
	static double maxLinkLoad =0;
	static double finalblocking = 0.0;
	static double finallengLst = 0.0;
	static double finalRunTime = 0.0;
	static int m1;//so function trong 1 demand
	
	static double[][] link_load;
	static boolean fl=false;
	static int flag = 0;
	static solSet _solSet;
	static int tau,noCoverFlow;
	static double s0Size;
	static double _gap;
	static double _nodeBB;
	static Double _acceptNo;
	static int _capChanging =0;
	static int _noLinkAdding =0;
	static int noSpine =0;
	static double spineRatio = 0;
	static int leafCapacity = 0;
	
	public static ArrayList<Integer> Sp_double(int src,int dest, GraphDouble _g,double maxBw)
	{

		ArrayList<Integer> _shortestPath = new ArrayList<Integer>();
		SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
        
		for (int j=0;j<_g.V();j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        //DefaultWeightedEdge[] e= new DefaultWeightedEdge[(g.getV()*(g.getV()-1))/2];
        //int id=0;        
        for (int j=0;j<_g.V();j++)
        {	        	
        	for(int k=0;k<_g.V();k++)
        	{
        		if(j!=k&&_g.getEdgeWeight(j+1, k+1)>maxBw)
        		{
        			DefaultWeightedEdge e=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		g_i.setEdgeWeight(e, _g.getEdgeWeight((j+1), (k+1)));
        		}
        	}
        }       
        List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+src, "node"+dest);
        int source;
		if(_p!=null)
		{
			_shortestPath.add(src);
			source=src;
			while (_p.size()>0)
			{	
				int ix =0;
				for(int l=0;l<_p.size();l++)
				{
					int int_s =Integer.parseInt(g_i.getEdgeSource(_p.get(l)).replaceAll("[\\D]", ""));
					int int_t =Integer.parseInt(g_i.getEdgeTarget(_p.get(l)).replaceAll("[\\D]", ""));
					if( int_s == source )
					{
						_shortestPath.add(int_t);
						source = int_t;
						ix = l;
						//_g.setEdgeWeight(int_s, int_t, _g.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
					if( int_t == source)
					{
						_shortestPath.add(int_s);
						source = int_s;
						ix = l;
						//_g.setEdgeWeight(int_s, int_t, _g.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
				}
				_p.remove(ix);
			}
			for(int _i:_shortestPath)
				{
					System.out.print(_i+",");
				}						
		}
		else
		{
			System.out.println("khong tim duoc duong di giua "+src+" va "+ dest);
			return null;
			
		}
        
        
		return _shortestPath;
	
	}
	public static ArrayList<Integer> ShortestPath(int src, int dest, MyGraph _g,double maxBw)
	{
		ArrayList<Integer> _shortestPath = new ArrayList<Integer>();
		SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
        
		for (int j=0;j<_g.V();j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        //DefaultWeightedEdge[] e= new DefaultWeightedEdge[(g.getV()*(g.getV()-1))/2];
        //int id=0;        
        for (int j=0;j<_g.V();j++)
        {	        	
        	for(int k=0;k<_g.V();k++)
        	{
        		if(j!=k&&_g.getEdgeWeight(j+1, k+1)>maxBw)
        		{
        			DefaultWeightedEdge e=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		g_i.setEdgeWeight(e, _g.getEdgeWeight((j+1), (k+1)));
        		}
        	}
        }       
        List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+src, "node"+dest);
        int source;
		if(_p!=null)
		{
			_shortestPath.add(src);
			source=src;
			while (_p.size()>0)
			{	
				int ix =0;
				for(int l=0;l<_p.size();l++)
				{
					int int_s =Integer.parseInt(g_i.getEdgeSource(_p.get(l)).replaceAll("[\\D]", ""));
					int int_t =Integer.parseInt(g_i.getEdgeTarget(_p.get(l)).replaceAll("[\\D]", ""));
					if( int_s == source )
					{
						_shortestPath.add(int_t);
						source = int_t;
						ix = l;
						//_g.setEdgeWeight(int_s, int_t, _g.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
					if( int_t == source)
					{
						_shortestPath.add(int_s);
						source = int_s;
						ix = l;
						//_g.setEdgeWeight(int_s, int_t, _g.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
				}
				_p.remove(ix);
			}
			for(int _i:_shortestPath)
				{
					System.out.print(_i+",");
				}						
		}
		else
		{
			System.out.println("khong tim duoc duong di giua "+src+" va "+ dest);
			return null;
			
		}
        
        
		return _shortestPath;
	}
	
	public static double getDelay(int id)
	{
		if(id==0) return -1;
		for(int i=0;i<m;i++)
			if (functionArr[i].id() ==id)
				return functionArr[i].getDelay();
		return -1;
	}
	public static double getReq(int id)
	{
		if(id==0) return -1;
		for(int i=0;i<m;i++)
			if (functionArr[i].id() ==id)
				return functionArr[i].getReq();
		return -1;
	}
	/**id is from 1 to m*/
	public static Function getFunction(int id)
	{
		if(id==0) return null;
		for(int i=0;i<m;i++)
			if (functionArr[i].id() ==id)
				return functionArr[i];
		return null;
	}
	
	public static double getBwService(int id)
	{
		if(id==0) return 0;
		for(int i=0;i<m;i++)
			if(demandArray.get(i).idS()==id)
				return demandArray.get(i).bwS();
		return -1;
	}
	public static double getRateService(int id)
	{
		if(id==0) return 0;
		for(int i=0;i<m;i++)
			if(demandArray.get(i).idS()==id)
				return demandArray.get(i).getRate();
		return -1;
	}
	/**id is from 1 to d*/
	public static Demand getDemand(int id)
	{
		for (int i=0;i<d;i++)
			if(demandArray.get(i).idS()==id)
				return demandArray.get(i);
		return null;
	}
	
	public static void ReadFileAndUpdate(String fileName)
	{
		m1=4;
		leafCapacity = 40;

		File file = new File(fileName);
		demandArray = new ArrayList<Demand>();
        try {
			in = new BufferedReader(new FileReader(file));
			String[] firstLine=in.readLine().split(" ");
			m= Integer.parseInt(firstLine[0]);
			d= Integer.parseInt(firstLine[1]);
			n= Integer.parseInt(firstLine[2]);
			E = Integer.parseInt(firstLine[3]);
			String[] line= new String[2*n+d+2];
			String thisLine=null;
			int k =0;
			while((thisLine = in.readLine()) !=null)
			{				
				line[k]=thisLine;
				k++;
			}
			functionArr= new Function[m];
			//demandArr = new Demand[d];
			
			//m function
			String[] lineFunc = line[0].split(";");
			for(int i = 0;i<m;i++)
			{ 
				functionArr[i]= new Function(i+1,Double.parseDouble(lineFunc[i].split(" ")[0]),Integer.parseInt(lineFunc[i].split(" ")[1]));
			}
			String[] tempLine;
			//d demand
			for (int i=0;i<d;i++)
			{
				tempLine = line[i+1].split(" ");
				Function[] f = new Function[tempLine.length-6];
				for (int j=0;j<f.length;j++)
					f[j]= getFunction(Integer.parseInt(tempLine[j+6]));
				Demand d_temp= new Demand(Integer.parseInt(tempLine[0]),Integer.parseInt(tempLine[1]),Integer.parseInt(tempLine[2]),Integer.parseInt(tempLine[3]),Double.parseDouble(tempLine[4]),Double.parseDouble(tempLine[5]),f);
				demandArray.add(d_temp);//				
			}
			//luu vao mang n+1 chieu
			ArrayList<Integer> cap = new ArrayList<>();
			ArrayList<ArrayList<Integer>> ww = new ArrayList<>();  				
			
			// virtual network
			int _capLink =0;
			int _capNode =0;
			int _totalLink=0;
			for (int i=0;i <n;i++)
			{
				if(_capNode==0&& Integer.parseInt(line[i+d+1])>0)
				{
					_capNode = Integer.parseInt(line[i+d+1]);
				}
	   	        cap.add(Integer.parseInt(line[i+d+1]));
			}
			
			for (int i=1;i<n+1;i++)
			{
				ArrayList<Integer> temp= new ArrayList<>();
				tempLine = line[i+d+n].split(" ");
				for(int j=1;j<n+1;j++)
				{
					temp.add(Integer.parseInt(tempLine[j-1]));
					if(Integer.parseInt(tempLine[j-1])>0)
					{
						_totalLink++;
						if(_capLink==0)
							_capLink = Integer.parseInt(tempLine[j-1]);
					}
				}
				ww.add(temp);
			}
			
			
			if(_capChanging==0)
			{
				if(_noLinkAdding!=0)
				{
					//Tăng thêm bao nhiêu link
					int _countLink=0;
					int _noLinkAd = _noLinkAdding*_totalLink/100;
					while (_countLink<_noLinkAd)
					{
						int _s = UtilizeFunction.randInt(0, n-1);
						int _t= UtilizeFunction.randInt(0, n-1);
						if(_s!=_t && ww.get(_s).get(_t)==0)
							ww.get(_s).set(_t, _capLink);
						else
							continue;
						_countLink++;
					}
				}
			}
			else
			{
				int _capChange = (_capChanging+ 100)*_capNode/100;
				for (int i=0;i <n;i++)
				{
					if(cap.get(i)!=0)
					{
						cap.set(i, _capChange);
					}
		   	        
				}
			}
			
			g= new MyGraph(cap,ww);
			
//			for (int i=0;i<n;i++)
//				for(int j=0;j<n;j++)
//				{
//					ultilize_resource += g.getEdgeWeight(i+1, j+1) * g.getPriceBandwidth() ;
//				}
			if (n*m <  m+4)
				_no=5;
			else
				_no = 5;
			x1= new GRBVar[d][m1][n];//binary
			y1= new GRBVar[d][n][n];//float (0,1)
			phi = new GRBVar[d][m1+1][n][n];
			blocking = new GRBVar[d];
			
            // Always close files.
            in.close();  
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	
	}
	public static void ReadInputFile(String fileName)
	{
		m1=4;
		leafCapacity = 40;
		File file = new File(fileName);
		demandArray = new ArrayList<Demand>();
        try {
			in = new BufferedReader(new FileReader(file));
			String[] firstLine=in.readLine().split(" ");
			m= Integer.parseInt(firstLine[0]);
			d= Integer.parseInt(firstLine[1]);
			n= Integer.parseInt(firstLine[2]);
			E = Integer.parseInt(firstLine[3]);
			String[] line= new String[2*n+d+2];
			String thisLine=null;
			int k =0;
			while((thisLine = in.readLine()) !=null)
			{				
				line[k]=thisLine;
				k++;
			}
			functionArr= new Function[m];
			//demandArr = new Demand[d];
			
			//m function
			String[] lineFunc = line[0].split(";");
			for(int i = 0;i<m;i++)
			{ 
				functionArr[i]= new Function(i+1,Double.parseDouble(lineFunc[i].split(" ")[0]),Integer.parseInt(lineFunc[i].split(" ")[1]));
			}
			String[] tempLine;
			//d demand
			for (int i=0;i<d;i++)
			{
				tempLine = line[i+1].split(" ");
				Function[] f = new Function[tempLine.length-6];
				for (int j=0;j<f.length;j++)
					f[j]= getFunction(Integer.parseInt(tempLine[j+6]));
				Demand d_temp= new Demand(Integer.parseInt(tempLine[0]),Integer.parseInt(tempLine[1]),Integer.parseInt(tempLine[2]),Integer.parseInt(tempLine[3]),Double.parseDouble(tempLine[4]),Double.parseDouble(tempLine[5]),f);
				demandArray.add(d_temp);//				
			}
			//luu vao mang n+1 chieu
			ArrayList<Integer> cap = new ArrayList<>();
			ArrayList<ArrayList<Integer>> ww = new ArrayList<>();  				
			
			// virtual network
			
			for (int i=0;i <n;i++)
			{
	   	        cap.add(Integer.parseInt(line[i+d+1]));
	   	        if(Integer.parseInt(line[i+d+1])>leafCapacity)
	   	        	noSpine++;
			}
			for (int i=1;i<n+1;i++)
			{
				ArrayList<Integer> temp= new ArrayList<>();
				tempLine = line[i+d+n].split(" ");
				for(int j=1;j<n+1;j++)
				{
					temp.add(Integer.parseInt(tempLine[j-1]));
				}
				ww.add(temp);
			}					
			g= new MyGraph(cap,ww);
			
//			for (int i=0;i<n;i++)
//				for(int j=0;j<n;j++)
//				{
//					ultilize_resource += g.getEdgeWeight(i+1, j+1) * g.getPriceBandwidth() ;
//				}
			if (n*m <  m+4)
				_no=5;
			else
				_no = 5;
			x1= new GRBVar[d][m1][n];//binary
			y1= new GRBVar[d][n][n];//float (0,1)
			phi = new GRBVar[d][m1+1][n][n];
			blocking = new GRBVar[d];
			
            // Always close files.
            in.close();  
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	//heuristic
	static int[][] Dist;
	public static boolean _Dist()
	{
		SimpleWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
		Dist = new int[g.V()+1][g.V()+1];
		for(int i=0;i<n+1;i++)
        	for (int j=0;j<n+1;j++)
        		Dist[i][j]=Integer.MAX_VALUE;
		for (int j=0;j<n;j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        DefaultWeightedEdge[] e= new DefaultWeightedEdge[(n*(n-1))/2];
        int id=0;
        
        for (int j=0;j<n-1;j++)
        {	        	
        	for(int k=j+1;k<n;k++)
        	{
        		e[id]=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
        		g_i.setEdgeWeight(e[id], g.getEdgeWeight((j +1), (k+1)));
        		id++;
        	}
        }
        for(int i=0;i<n-1;i++)
        	for (int j=i+1;j<n;j++)
        	{
        		List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+(i+1), "node"+(j+1));
        		if(_p!=null)
        		{
        			Dist[i+1][j+1]=_p.size()+1;
        			Dist[j+1][i+1]=_p.size()+1;
        		}
        		else
        		{
        			Dist[i+1][j+1]=Integer.MAX_VALUE;
        			Dist[j+1][i+1]=Integer.MAX_VALUE;
        		}
        	} 
        return true;
        
	}
	
	static double functionCost=0.0;
	static ArrayList<ArrayList<Integer>> srcLst;
	static ArrayList<ArrayList<Integer>> destLst;
	static ArrayList<Integer> exLst;
	public static void clustering(int numCluster)
	{
		ArrayList<ArrayList<Integer>> c = new ArrayList<>();
		for(int i=0;i<numCluster;i++)
		{
			ArrayList<Integer> nodeLst = new ArrayList<>();
		}
	}
	static ArrayList<Integer> setOFEndPoint;
	static ArrayList<Integer> sortingNode (ArrayList<Integer> _nodeLst)
	{
		ArrayList<Integer> id = new ArrayList<>();
		while(true)
		{
			int max=-1;
			int maxID = -1;
			for(int i=0;i<_nodeLst.size();i++)
			{
				if(_nodeLst.get(i)>max)
				{
					max = _nodeLst.get(i);
					maxID = i;
				}
			}
			if(maxID!=-1)
			{
				id.add(maxID+1);
				_nodeLst.set(maxID, -1);
			}
			else
				break;	
			
		}
		return id;
		
	}
	static int distanceCluster(ArrayList<Integer> s1, ArrayList<Integer> s2, MyGraph _g)
	{
		int minVal = Integer.MAX_VALUE;
		
		for(int i=0;i<s1.size();i++)
		{
			for(int j=0;j<s1.size();j++)
			{
				if(_g.getEdgeWeight(s1.get(i), s1.get(j))>0 && _g.getEdgeWeight(s1.get(i), s1.get(j))<minVal)
					minVal = _g.getEdgeWeight(s1.get(i), s1.get(j));
			}
		}
		for(int i=0;i<s2.size();i++)
		{
			for(int j=0;j<s2.size();j++)
			{
				if(_g.getEdgeWeight(s2.get(i), s2.get(j))>0 && _g.getEdgeWeight(s2.get(i), s2.get(j))<minVal)
					minVal = _g.getEdgeWeight(s2.get(i), s2.get(j));
			}
		}
		if(s1.size()==1&&s2.size()==1)
			minVal=0;
		
		for(int i=0;i<s1.size();i++)
		{
			for(int j=0;j<s2.size();j++)
			{
				if(_g.getEdgeWeight(s1.get(i), s2.get(j))>0 && _g.getEdgeWeight(s1.get(i), s2.get(j))>minVal)
					minVal = _g.getEdgeWeight(s1.get(i), s2.get(j));
			}
		}
		if(minVal>0)
			return minVal;
		else
			return -1;
	}
	static ArrayList<ArrayList<Integer>> superUpdateCluster(ArrayList<ArrayList<Integer>> lst, MyGraph _g)
	{
		ArrayList<ArrayList<Integer>> fiCluster = new ArrayList<>();
		ArrayList<ArrayList<Integer>> groups = new ArrayList<>();
		
		for(int i=0;i<lst.size()-1;i++)
		{
			ArrayList<Integer> dist = new ArrayList<>();
			ArrayList<Integer> t = new ArrayList<>();
			for(int j=i+1;j<lst.size();j++)
			{
				dist.add(distanceCluster(lst.get(i), lst.get(j), _g));
			}
			int max =Collections.max(dist);
			for(int j=0;j<dist.size();j++)
			{
				if(dist.get(j)==max)
					t.add(j+i+1);
					
			}
			groups.add(t);
		}
//		for(int i=0;i<groups.size();i++)
//		{
//			ArrayList<Integer> gr = groups.get(i);
//			for(int j=0;j<gr.size();j++)
//			{
//				ArrayList<Integer> subgr = groups.get(gr.get(j));
//				for(int set:subgr)
//				{
//					gr.add(set);
//				}
//			}
//		}
		
		return fiCluster;
	}
	static ArrayList<ArrayList<Integer>> updateCluster(ArrayList<ArrayList<Integer>> _cluster,ArrayList<Integer> groupCls,int _n)
	{
		ArrayList<ArrayList<Integer>> fiCluster = new ArrayList<>();
		ArrayList<Integer> cls = new ArrayList<>();
		cls.add(_n);
		for(int i=0;i<groupCls.size();i++)
		{
			ArrayList<Integer> t = _cluster.get(groupCls.get(i));
			
			for(int j =0;j<t.size();j++ )
				cls.add(t.get(j));
		}
		fiCluster.add(cls);
		for(int i=0;i<_cluster.size();i++)
		{			
			if(!groupCls.contains(i))
			{
				cls = new ArrayList<>();
				ArrayList<Integer> t = _cluster.get(i);
				for(int j =0;j<t.size();j++ )
					cls.add(t.get(j));
				fiCluster.add(cls);
			}
			
		}
		return fiCluster;
	}

	//giai thuat cluster 2

	static double maximumLink = 0;
	static double maximumNode=0;
	public static int numberOfTimes(int id, ArrayList<Integer> arr)
	{
		int num = 0;
		for(int i=0;i<arr.size();i++)
			if(arr.get(i)==id)
				num++;
		return num;
	}
	public static int min_hop_back(ArrayList<Integer> _nLst, MyGraph _g,int _n)
	{
		int minVal = -1;
		DirectedGraph<String, DefaultEdge> g_i = new DefaultDirectedGraph<>(DefaultEdge.class);
		List<String> vertexList = new ArrayList<String>();
		g_i.addVertex("node0");
		vertexList.add("node0");
		for (int i = 0; i < _nLst.size(); i++) {
				int s= i+1;
				vertexList.add("node"+s);
				g_i.addVertex("node"+s);
		}
		for(int i=0;i<_nLst.size();i++)
		{
			for(int j=0;j<_nLst.size();j++)
			{
				if(i!=j && _g.getEdgeWeight(_nLst.get(i), _nLst.get(j))>0)
					g_i.addEdge(vertexList.get(i+1), vertexList.get(j+1));
			}
			if(_g.getEdgeWeight(_nLst.get(i),_n)>0)
				g_i.addEdge(vertexList.get(i+1),vertexList.get(0));
		}
		for(int i=0;i<_nLst.size();i++)
		{
			DijkstraShortestPath<String, DefaultEdge> dj= new DijkstraShortestPath<String, DefaultEdge>(g_i, vertexList.get(i+1), vertexList.get(0));
			if(dj.getPath()!=null)
			{
				Double len = dj.getPathLength();
				if(minVal==-1)
					minVal= len.intValue();
				else
					if(len.intValue()<minVal)
						minVal= len.intValue();
			}
			
		}	
		return minVal;
	
	}
	public static ArrayList<Integer> SP(int src, int dest, ArrayList<Integer> lst, MyGraph _g,int bw,int lengF)
	{
		ArrayList<Integer> temp = new ArrayList<>();
		SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class);
		
		//DirectedGraph<String, DefaultEdge> g_i = new DefaultDirectedGraph<>(DefaultEdge.class);
		List<String> vertexList = new ArrayList<String>();
		g_i.addVertex("node"+src);
		g_i.addVertex("node"+dest);
		vertexList.add("node" + src);
		vertexList.add("node" + dest);
		for (int i = 0; i < lst.size(); i++) {
				int s= lst.get(i);
				vertexList.add("node"+s);
				g_i.addVertex("node"+s);
		}
		for(int i=0;i<lst.size();i++)
		{
			for(int j=0;j<lst.size();j++)
			{
				if(i!=j && _g.getEdgeWeight(lst.get(i), lst.get(j))>=bw)
				{
					
					DefaultWeightedEdge e=g_i.addEdge(vertexList.get(i+2), vertexList.get(j+2));   
					double w = maximumLink*1.0/_g.getEdgeWeight(lst.get(i), lst.get(j))+lengF*maximumNode*1.0/_g.getCap(lst.get(j));
					g_i.setEdgeWeight(e, w);
				}
			}
			if(_g.getEdgeWeight(src, lst.get(i))>=bw)
			{
				DefaultWeightedEdge e=g_i.addEdge(vertexList.get(0), vertexList.get(i+2));   
				double w = maximumLink*1.0/_g.getEdgeWeight(src, lst.get(i))+lengF*maximumNode*1.0/_g.getCap(lst.get(i));
				g_i.setEdgeWeight(e, w);
			}
			if(_g.getEdgeWeight(lst.get(i), dest)>=bw)
			{
				//g_i.addEdge(vertexList.get(i+2), vertexList.get(1));
				DefaultWeightedEdge e=g_i.addEdge(vertexList.get(i+2), vertexList.get(1)); 
				double w = maximumLink*1.0/_g.getEdgeWeight(lst.get(i),dest)+lengF*maximumNode*1.0/_g.getCap(dest);
				g_i.setEdgeWeight(e, w);
			}
		}
		List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, vertexList.get(0),vertexList.get(1));
		if(_p!=null && _p.size()>0)
		{
			for(DefaultWeightedEdge e: _p)
			{
				int int_s =Integer.parseInt(g_i.getEdgeSource(e).replaceAll("[\\D]", ""));
				temp.add(int_s);
			}
			temp.add(dest);		
		}
		
		return temp;
	}
	public static int min_hop(int _n, ArrayList<Integer> _nLst, MyGraph _g)
	{	

		int minVal = -1;
		DirectedGraph<String, DefaultEdge> g_i = new DefaultDirectedGraph<>(DefaultEdge.class);
		List<String> vertexList = new ArrayList<String>();
		g_i.addVertex("node0");
		vertexList.add("node0");
		for (int i = 0; i < _nLst.size(); i++) {
				int s= i+1;
				vertexList.add("node"+s);
				g_i.addVertex("node"+s);
		}
		for(int i=0;i<_nLst.size();i++)
		{
			for(int j=0;j<_nLst.size();j++)
			{
				if(i!=j && _g.getEdgeWeight(_nLst.get(i), _nLst.get(j))>0)
					g_i.addEdge(vertexList.get(i+1), vertexList.get(j+1));
			}
			if(_g.getEdgeWeight(_n, _nLst.get(i))>0)
				g_i.addEdge(vertexList.get(0), vertexList.get(i+1));
		}
		FloydWarshallShortestPaths<String, DefaultEdge> floyd = new FloydWarshallShortestPaths<>(g_i);
		List<GraphPath<String,DefaultEdge>> allPaths = floyd.getShortestPaths(vertexList.get(0));
		if(allPaths !=null && allPaths.size()>0)
		{
			minVal = allPaths.get(0).getEdgeList().size();
			for(GraphPath<String,DefaultEdge> p: allPaths)
			{
				if(p.getEdgeList().size()<minVal)
					minVal = p.getEdgeList().size();
			}
			return minVal;
		}
		
		return -1;
	}

	static ArrayList<ArrayList<Integer>> partitionNode2(MyGraph _g,int _k)
	{
		//_k la gia tri clusters khoi tao
		ArrayList<ArrayList<Integer>> clusters = new ArrayList<>();
		d= demandArray.size();
		ArrayList<Integer> _cap = new ArrayList<>();
		for(int i=0;i<_g.K.size();i++)
			_cap.add(_g.K.get(i));
		
		ArrayList<Integer> nodeLst = sortingNode(_cap);
		int id = 0;
		for(int i=0;i<_k;i++)
		{
			ArrayList<Integer> temp = new ArrayList<>();
			for(int j = id;j<nodeLst.size();j++)
			{
				if(!setOFEndPoint.contains(nodeLst.get(j)))
				{
					temp.add(nodeLst.get(j));
					id = j+1;
					break;
				}
			}
			clusters.add(temp);
		}
		ArrayList<Integer> nodeRemaining = new ArrayList<>();
		for(int j=id;j<nodeLst.size();j++)
		{
			if(!setOFEndPoint.contains(nodeLst.get(j)))
				nodeRemaining.add(nodeLst.get(j));
		}
		
		for(int i=0;i<nodeRemaining.size();i++)
		{
			int _n = nodeRemaining.get(i);
			if(!setOFEndPoint.contains(_n))
			{
				int max =-1;
				ArrayList<Integer> ClustLst = new ArrayList<>();
				for(int j=0;j<clusters.size();j++)
				{
					ArrayList<Integer> cls = clusters.get(j);
					for (int k=0;k<cls.size();k++)
					{
						if(_g.getEdgeWeight(_n, cls.get(k))>0 || _g.getEdgeWeight(cls.get(k),_n)>0 )
						{
							if(_g.getEdgeWeight(_n, cls.get(k))>max || _g.getEdgeWeight(cls.get(k),_n)>max )
							{
								ClustLst = new ArrayList<>();
								max = _g.getEdgeWeight(_n, cls.get(k));
								ClustLst.add(j);
							}
							else
							{
								if(_g.getEdgeWeight(_n, cls.get(k))==max || _g.getEdgeWeight(cls.get(k),_n)==max )
								{
									if(!ClustLst.contains(j))
										ClustLst.add(j);
								}
							}
						}
						
					}
				}
				clusters = updateCluster(clusters, ClustLst,_n);	
			}
					
		}
		
		
		return clusters;	
	}
	public static void clusteringMethod2(String outFile)
	{

		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	      MyGraph g_edit = new MyGraph(g.K, g.w);	
	       	
		//thuc hien o day
	       	
	       
	       	for (int i=0;i<g_edit.V();i++)
	       		for(int j=0;j<g_edit.V();j++)
	       			if(g_edit.getEdgeWeight(i+1, j+1)>maximumLink)
	       				maximumLink = g_edit.getEdgeWeight(i+1, j+1);
	       	for (int i=0;i<g_edit.V();i++)
	       		if(g_edit.getCap(i+1)>maximumNode)
	       			maximumNode= g_edit.getCap(i+1);
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	
	       		       	
	       	setOFEndPoint = new ArrayList<>();
			for(int i=0;i<d;i++)
			{
				Demand _d = demandArray.get(i);
				if(!setOFEndPoint.contains(_d.sourceS()))
					setOFEndPoint.add(_d.sourceS());
				if(!setOFEndPoint.contains(_d.destinationS()))
					setOFEndPoint.add(_d.destinationS());	
			}
			
			int numCluster = (g.V()-setOFEndPoint.size())/2;
			
	       	//phan cum
			
			
			for(int i=0;i<demandArray.size();i++)
			{
				
				Demand _d = demandArray.get(i);
				int src=_d.sourceS();
				int dest = _d.destinationS();
				//setOFEndPoint = new ArrayList<>();
				//setOFEndPoint.add(src);
				//setOFEndPoint.add(dest);
				//int numCluster = (g.V()-setOFEndPoint.size())/2;
				ArrayList<ArrayList<Integer>> clusters = partitionNode2(g_edit, numCluster);
				int minHops = Integer.MAX_VALUE;
				ArrayList<Integer> cluster_i = new ArrayList<>();
				int idCluster = -1;
				for (int j=0;j<clusters.size();j++)
				{
					int s1 = min_hop(src, clusters.get(j), g);
					int s2=	min_hop_back(clusters.get(j), g, dest);
					if(s1>=0 && s2>=0)
					{
						if(s1+s2<minHops)
						{
							idCluster = j;
							minHops = s1+s2;
						}
					}
				
				}
				if(idCluster==-1)
					return;
				else
					cluster_i = clusters.get(idCluster);
				
				//clusters = superUpdateCluster(clusters, g_edit);
				//
				ArrayList<Integer> p = SP(src,dest,cluster_i,g_edit,_d.bwS(),_d.getFunctions().length);
				if(p!=null)
				{
					sol.add(p);
					for(int j=0;j<p.size()-1;j++)
					{
						int w = g_edit.getEdgeWeight(p.get(j), p.get(j+1));
						g_edit.setEdgeWeight(p.get(j), p.get(j+1), w);
					}
				}
				
			}
			
			
	      //place function + update resource
	       	int sum_cap = 0;
	       	ArrayList<Integer> setNode = new ArrayList<>();
	       	ArrayList<Integer> setDiffNode = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			
	       			setNode.add(sol.get(i).get(j));
	       			if(!setDiffNode.contains(sol.get(i).get(j)))
	       			{
	       				setDiffNode.add(sol.get(i).get(j));
	       				sum_cap+=g_edit.getCap(sol.get(i).get(j));
	       			}
	       		}
	       	}
	       	
	    	ArrayList<ArrayList<Integer>> times = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			int num= numberOfTimes(sol.get(i).get(j),setNode);
	       			ti.add(num);
	       		}
	       		times.add(ti);
	       	}
	       	
	       	int sum_req = 0;
	       	for(int i=0;i<demandArray.size();i++)
	       	{
	       		Function[] fArr = demandArray.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	       		
	       	}
	       	double idealNodeLoad = sum_req*1.0/sum_cap +0.1;
	       	
	       
	       	ArrayList<Integer[]> funLoc = new ArrayList<>();
	       	
	       	ArrayList<ArrayList<Integer>> capSol = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			ti.add(g_edit.getCap(sol.get(i).get(j))/times.get(i).get(j));
	       		}
	       		capSol.add(ti);
	       	}
	       	ArrayList<Integer> idCapLst = new ArrayList<>();
	       	ArrayList<Integer> avaiCapLst = new ArrayList<>();
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		//for each demand
	       		ArrayList<Integer> p = sol.get(i);
	       		Function[] fArr = demandArray.get(i).getFunctions();
	       		Integer[] locF = new Integer[fArr.length];
	       		int id=0;
	       		for (int j1=0;j1<p.size();j1++)
	       		{
	       			int cap_j = capSol.get(i).get(j1);
	       			if(idCapLst.contains(p.get(j1)))
	       			{
	       				int index = idCapLst.indexOf(p.get(j1));
	       				cap_j+=avaiCapLst.get(index);
	       				idCapLst.remove(index);
	       				avaiCapLst.remove(index);
	       			}
	       			double loaded =0.0;
	       			for(int j2=id;j2<fArr.length;j2++)
		       		{
	       				loaded+= fArr[j2].getReq()*1.0;
		       			if(loaded/cap_j<idealNodeLoad || j1==p.size()-1)
		       			{
		       				locF[j2] = p.get(j1);
		       				if(cap_j-fArr[j2].getReq()>=0)
		       				{
		       					capSol.get(i).set(j1, cap_j-fArr[j2].getReq());	
		       				}
		       				else
		       				{
		       					System.out.println("Demand nay khong thoa man");
		       					return;
		       				}
		       				id++;
		       			}
		       			else
		       			{
		       				//thua cap thi cho lai bon dang sau
		       				Double capLeft = capSol.get(i).get(j1)/(idealNodeLoad) - cap_j ;
		       				if (capLeft>0)
		       				{
			       				idCapLst.add(p.get(j1));		       						       				
		       					avaiCapLst.add(capLeft.intValue());
		       				}
		       				break;
		       			}
		       		}
	       		}
	       		
	       		funLoc.add(locF);
	       		
	       	}
	       	//ket qua o sol and funcLoc
	       	maxLinkLoad = 0.0;
	       	maxNodeLoad = 0.0;
	       	ArrayList<ArrayList<Integer>> usedBand = new ArrayList<>();
	       	ArrayList<Integer> usedReq = new ArrayList<>();
	       	for(int i=0;i<g.V();i++)
	       	{
	       		usedReq.add(0);
	       		ArrayList<Integer> te= new ArrayList<>();
	       		for(int j=0;j<g.V();j++)
	       		{
	       			te.add(0);
	       		}
	       		usedBand.add(te);
	       	}
	       	for(int i=0;i<demandArray.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size()-1;j++)
	       		{
	       			int _usedW = usedBand.get(sol.get(i).get(j)-1).get(sol.get(i).get(j+1)-1)+demandArray.get(i).bwS();
	       			usedBand.get(sol.get(i).get(j)-1).set(sol.get(i).get(j+1)-1, _usedW);
	       		}
	       		Function[] fArr = demandArray.get(i).getFunctions();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			int node = funLoc.get(i)[j];	       			
	       			int _usedReq = usedReq.get(node-1) + fArr[j].getReq();
	       			usedReq.set(node-1, _usedReq);
	       		}
	       	}
	       	for(int i=0;i<g.V();i++)
	       	{
	       		for(int j=0;j<g.V();j++)
	       		{
	       			double linkLoad = usedBand.get(i).get(j)*1.0/g.getEdgeWeight(i+1, j+1);
	       			if(linkLoad>maxLinkLoad)
	       				maxLinkLoad = linkLoad;
	       		}
	       		double nodeLoad = usedReq.get(i)*1.0/g.getCap(i+1);
	       		if(nodeLoad>maxNodeLoad)
	       			maxNodeLoad = nodeLoad;
	       	}
	       	
	       	
	       	out.write("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	out.newLine();
	       	for(int i=0;i<demandArray.size();i++)
	       	{
	       		out.write("Demand "+ demandArray.get(i).idS()+":");
	       		out.newLine();
	       		out.write("Path:");
	       		out.newLine();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			out.write(sol.get(i).get(j)+ " ");
	       		}
	       		out.newLine();
	       		out.write("Function Location: ");
	       		out.newLine();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			out.write(funLoc.get(i)[j]+" ");
	       		}
	       		out.newLine();
	       	}
	       	
	       	
	       	
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	}
	
	//Giai thuat tao graph bang viec chia tung tap dinh dau va dinh cuoi cua demand
	
	public static void partitionNode(MyGraph _g)
	{
		d= demandArray.size();
		srcLst = new ArrayList<>();
		destLst = new ArrayList<>();
		exLst = new ArrayList<>();
		for(int i=0;i<d;i++)
		{
			Demand _d = demandArray.get(i);			
			srcLst.add(new ArrayList<>(Arrays.asList(_d.sourceS())));
			destLst.add(new ArrayList<>(Arrays.asList(_d.destinationS())));			
		}
		for(int i=0;i<_g.V();i++)
		{
			int maxID1 = -1;
			int maxVal= -1;
			int maxIDlst = -1;
			for(int j=0;j<srcLst.size();j++)
			{
				int _s = srcLst.get(j).get(0);
				int _w = _g.getEdgeWeight(_s, i+1);
				if(_w>0 && _w>maxVal)
				{
					maxVal = _w;
					maxID1 = j;
				}
//				
//				for(int k=0;k<srcLst.get(j).size();k++)
//				{
//					int _s = srcLst.get(j).get(k);
//					int _w = g.getEdgeWeight(_s, i+1);
//					if(_w>0 &&_w>maxVal)
//					{
//						maxVal = _w;
//						maxID = j;
//						maxIDlst=_s;
//					}
//				}
				
			}
			if(maxID1!=-1)
			{
				for(int j=0;j<srcLst.size();j++)
				{
					int _n = srcLst.get(j).get(0);
					if(_n==srcLst.get(maxID1).get(0))
					{
						ArrayList<Integer> _t = srcLst.get(j);
						//neu maxID co o nhieu srclst -> add vao het
						_t.add(i+1);
						srcLst.set(j,_t);
					}
//					for(int k=0;k<srcLst.get(j).size();k++)
//					{
//						int _n = srcLst.get(j).get(k);
//						if(_n==maxIDlst)
//						{
//							ArrayList<Integer> _t = srcLst.get(j);
//							//neu maxID co o nhieu srclst -> add vao het
//							_t.add(i+1);
//							srcLst.set(j,_t);
//							break;
//						}
//					}
//					
				}
			}
			int maxID2 =-1;
			maxVal =-1;
			maxIDlst=-1;
			for(int j=0;j<destLst.size();j++)
			{
				int _d = destLst.get(j).get(0);
				int _w = _g.getEdgeWeight(i+1,_d);
				if(_w>0 && _w>maxVal)
				{
					maxVal = _w;
					maxID2 = j;
				}
//				for(int k=0;k<destLst.get(j).size();k++)
//				{
//					int _d = destLst.get(j).get(k);
//					int _w = g.getEdgeWeight(i+1,_d);
//					if(_w>0 &&_w>maxVal)
//					{
//						maxVal = _w;
//						maxID = j;
//						maxIDlst=_d;
//					}
//				}
				
			}
			if(maxID2!=-1)
			{
				for(int j=0;j<destLst.size();j++)
				{
					int _n= destLst.get(j).get(0);
					if(_n==destLst.get(maxID2).get(0))
					{
						ArrayList<Integer> _t = destLst.get(j);
						_t.add(i+1);
						destLst.set(j, _t);
					}
//					for(int k=0;k<destLst.get(j).size();k++)
//					{
//						int _n= destLst.get(j).get(k);
//						if(_n==maxIDlst)
//						{
//							ArrayList<Integer> _t = destLst.get(j);
//							_t.add(i+1);
//							destLst.set(j, _t);
//							break;
//						}
//					}
					
				}
			}
			if(maxID1==-1 && maxID2==-1)
				exLst.add(i+1);
		}
	}
	public static int MinimalConnect(ArrayList<Integer> s1, ArrayList<Integer> s2,MyGraph _g)
	{
		int min = Integer.MAX_VALUE;
		boolean ok = false;
		for(int i=0;i<s1.size();i++)
			for(int j=0;j<s2.size();j++)
			{
				int _w = _g.getEdgeWeight(s1.get(i), s2.get(j));
				if(_w!=0 && _w<min)
				{
					ok=true;
					min = _w;
				}
			}
		if(!ok)
			min=-1;
		return min;
	}
	
	//Tao graph voi dinh dai dien cho cac tap, canh la gia tri nho nhat cua link noi giua 2 tap.
	public static GraphDouble CreateNodeGraph(MyGraph _g)
	{
		ArrayList<ArrayList<Integer>> temp = new ArrayList<>();
		ArrayList<Double> _cap = new ArrayList<>();
		ArrayList<ArrayList<Double>> _w= new ArrayList<>();
	
		for(int i=0;i<srcLst.size();i++)
		{
			temp.add(srcLst.get(i));
			_cap.add(10.0);
		}
		for(int i=0;i<destLst.size();i++)
		{
			temp.add(destLst.get(i));
			_cap.add(10.0);
		}
		temp.add(exLst);
		_cap.add(10.0);
		for(int i=0;i<temp.size();i++)
		{
			ArrayList<Double> _wTemp = new ArrayList<>();
			for(int j=0;j<temp.size();j++)
			{
				_wTemp.add(-1.0);
				
			}
			_w.add(_wTemp);
		}
		for(int i=0;i<srcLst.size();i++)
		{
			ArrayList<Double> _wTemp = _w.get(i);
			for(int j=0;j<temp.size();j++)
			{
				if(i!=j)
				{
					ArrayList<Integer> si=srcLst.get(i);
					ArrayList<Integer> sj = temp.get(j);
					int minimal = MinimalConnect(si, sj,_g);		
					_wTemp.set(j, maximumLink*1.0/minimal);	
				}
							
				
			}
			_w.set(i, _wTemp);
		}
		for(int j=0;j<temp.size();j++)
		{
			ArrayList<Double> _wTemp = _w.get(j);
			for(int i=0;i<destLst.size();i++)
			{
				if(i!=j-srcLst.size())
				{
					ArrayList<Integer> si=destLst.get(i);
					ArrayList<Integer> sj = temp.get(j);
					int minimal = MinimalConnect(sj, si,_g);		
					_wTemp.set(i+srcLst.size(), maximumLink*1.0/minimal);	
				}
			}
			_w.set(j, _wTemp);
		}
		
		GraphDouble gNode = new GraphDouble(_cap, _w);
		return gNode;
		
	}

	public static GraphDouble GraphCombination(ArrayList<ArrayList<Integer>> set,int bw,MyGraph _g)
	{
		ArrayList<Double> _cap = new ArrayList<>();
		ArrayList<ArrayList<Double>> _w= new ArrayList<>();
	
		for(int i=0;i<_g.V();i++)
		{
			_cap.add(_g.getCap(i+1)*1.0);
		}
		for(int i=0;i<_g.V();i++)
		{
			ArrayList<Double> _wTemp = new ArrayList<>();
			for(int j=0;j<_g.V();j++)
			{
				_wTemp.add(-1.0);
			}
			_w.add(_wTemp);
		}
		for(int i=0;i<set.size();i++)
		{
			for(int j1=0;j1<set.get(i).size();j1++)
			{
				for(int j2=0;j2<set.get(i).size();j2++)
				{
					int u = set.get(i).get(j1);
					int v = set.get(i).get(j2);
					if(_g.getEdgeWeight(u,v)>=bw)
					{
						if(_g.getCap(v)>0)
						{
							_w.get(u-1).set(v-1, maximumNode*1.0/_g.getCap(v));
							//_w.get(u-1).set(v-1, maximumLink*1.0/_g.getEdgeWeight(u, v)+maximumNode*1.0/_g.getCap(v));
						}
						
					}
				}
			}
		}
		for(int i1=0;i1<set.size();i1++)
		{
			ArrayList<Integer> s1 = set.get(i1);
			for(int i2=0;i2<set.size();i2++)
			{
				if(i1!=i2)
				{
					ArrayList<Integer> s2 = set.get(i2);
					for(int j1 =0;j1<s1.size();j1++)
						for(int j2=0;j2<s2.size();j2++)
						{
							int u = s1.get(j1);
							int v = s2.get(j2);
							if(_g.getEdgeWeight(u,v)>=bw)
							{
								if(_g.getCap(v)>0)
								{
									//_w.get(u-1).set(v-1, maximumLink*1.0/_g.getEdgeWeight(u, v)+maximumNode*1.0/_g.getCap(v));
									_w.get(u-1).set(v-1, maximumNode*1.0/_g.getCap(v));
								}
							}
								
							if(_g.getEdgeWeight(v,u)>=bw)
								if(_g.getCap(u)>0)
									_w.get(v-1).set(u-1, maximumNode*1.0/_g.getCap(v));
									//_w.get(v-1).set(u-1, maximumLink*1.0/_g.getEdgeWeight(u, v)+maximumNode*1.0/_g.getCap(v));
							
						}
				}
			}
		}
		
		GraphDouble gNode = new GraphDouble(_cap, _w);
		return gNode;
	}
	
	public static void clusteringMethod(String outFile)
	{
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	      MyGraph g_edit = new MyGraph(g.K, g.w);	
	       	
		//thuc hien o day
	       	
	       
	       	for (int i=0;i<g_edit.V();i++)
	       		for(int j=0;j<g_edit.V();j++)
	       			if(g_edit.getEdgeWeight(i+1, j+1)>maximumLink)
	       				maximumLink = g_edit.getEdgeWeight(i+1, j+1);
	       	for (int i=0;i<g_edit.V();i++)
	       		if(g_edit.getCap(i+1)>maximumNode)
	       			maximumNode= g_edit.getCap(i+1);
	       	//maximumLink += 100;
	       	//maximumNode+=10;
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	
	       	
	       	//xet tung demand
	       	
	       	for (int i=0;i<demandArray.size();i++)
	       	{
	       		partitionNode(g_edit);
	       		GraphDouble gNode = CreateNodeGraph(g_edit);//do thi gia
	       		ArrayList<Integer> pathSet = Sp_double(i+1, i+demandArray.size()+1, gNode, 0);
	       		ArrayList<ArrayList<Integer>> setPar = new ArrayList<>();
	       		for(int j=0;j<pathSet.size();j++)
	       		{
	       			int setNo = pathSet.get(j);
	       			if(setNo > demandArray.size())
	       				setPar.add(destLst.get(setNo - demandArray.size()-1) );
	       			else
	       				setPar.add(srcLst.get(setNo-1));
	       		}
	       		GraphDouble g_tem= GraphCombination(setPar,demandArray.get(i).bwS(),g_edit);
	       		ArrayList<Integer> pathSol = Sp_double(demandArray.get(i).sourceS(), demandArray.get(i).destinationS(), g_tem,0);
	       		int dem=0;
	       		while(pathSol==null && dem<10)
	       		{
	       			dem++;
	       			gNode.setEdgeWeight(pathSet.get(0), pathSet.get(1),gNode.getEdgeWeight(pathSet.get(0), pathSet.get(1))*5);
//	       			for(int j=0;j<pathSet.size()-1;j++)
//		       		{
//	       				gNode.setEdgeWeight(pathSet.get(j), pathSet.get(j+1),gNode.getEdgeWeight(pathSet.get(j), pathSet.get(j+1))*100);
//		       		}	       			
	       			pathSet = Sp_double(i+1, i+demandArray.size()+1, gNode, 0);
		       		setPar = new ArrayList<>();
		       		for(int j=0;j<pathSet.size();j++)
		       		{
		       			int setNo = pathSet.get(j);
		       			if(setNo > demandArray.size())
		       			{
		       				if(setNo>2*demandArray.size())
		       					setPar.add(exLst);
		       				else
		       					setPar.add(destLst.get(setNo - demandArray.size()-1) );
		       			}
		       			else
		       				setPar.add(srcLst.get(setNo-1));
		       		}
	       			g_tem= GraphCombination(setPar,demandArray.get(i).bwS(),g_edit);
		       		pathSol = Sp_double(demandArray.get(i).sourceS(), demandArray.get(i).destinationS(), g_tem,0);
	       		}
	       		if(pathSol ==null)
	       		{
	       			System.out.println("Khong tim ra giai phap");
	       			return;
	       		}
	       			
	       		System.out.println("Length:" + pathSol.size());
	       		
	       		for(int j=0;j<pathSol.size()-1;j++)
	       		{
	       			int leftW = g_edit.getEdgeWeight(pathSol.get(j), pathSol.get(j+1)) - demandArray.get(i).bwS();
	       			g_edit.setEdgeWeight(pathSol.get(j), pathSol.get(j+1), leftW);
	       		}
	       		sol.add(pathSol);
	       	}
	       	
	      //place function + update resource
	       	int sum_cap = 0;
	       	ArrayList<Integer> setNode = new ArrayList<>();
	       	ArrayList<Integer> setDiffNode = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			
	       			setNode.add(sol.get(i).get(j));
	       			if(!setDiffNode.contains(sol.get(i).get(j)))
	       			{
	       				setDiffNode.add(sol.get(i).get(j));
	       				sum_cap+=g_edit.getCap(sol.get(i).get(j));
	       			}
	       		}
	       	}
	       	
	    	ArrayList<ArrayList<Integer>> times = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			int num= numberOfTimes(sol.get(i).get(j),setNode);
	       			ti.add(num);
	       		}
	       		times.add(ti);
	       	}
	       	
	       	int sum_req = 0;
	       	for(int i=0;i<demandArray.size();i++)
	       	{
	       		Function[] fArr = demandArray.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	       		
	       	}
	       	double idealNodeLoad = sum_req*1.0/sum_cap +0.1;
	       	
	       
	       	ArrayList<Integer[]> funLoc = new ArrayList<>();
	       	
	       	ArrayList<ArrayList<Integer>> capSol = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			ti.add(g_edit.getCap(sol.get(i).get(j))/times.get(i).get(j));
	       		}
	       		capSol.add(ti);
	       	}
	       	ArrayList<Integer> idCapLst = new ArrayList<>();
	       	ArrayList<Integer> avaiCapLst = new ArrayList<>();
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		//for each demand
	       		ArrayList<Integer> p = sol.get(i);
	       		Function[] fArr = demandArray.get(i).getFunctions();
	       		Integer[] locF = new Integer[fArr.length];
	       		int id=0;
	       		for (int j1=0;j1<p.size();j1++)
	       		{
	       			int cap_j = capSol.get(i).get(j1);
	       			if(idCapLst.contains(p.get(j1)))
	       			{
	       				int index = idCapLst.indexOf(p.get(j1));
	       				cap_j+=avaiCapLst.get(index);
	       				idCapLst.remove(index);
	       				avaiCapLst.remove(index);
	       			}
	       			double loaded =0.0;
	       			for(int j2=id;j2<fArr.length;j2++)
		       		{
	       				loaded+= fArr[j2].getReq()*1.0;
		       			if(loaded/cap_j<idealNodeLoad || j1==p.size()-1)
		       			{
		       				locF[j2] = p.get(j1);
		       				if(cap_j-fArr[j2].getReq()>=0)
		       				{
		       					capSol.get(i).set(j1, cap_j-fArr[j2].getReq());	
		       				}
		       				else
		       				{
		       					System.out.println("Demand nay khong thoa man");
		       					return;
		       				}
		       				id++;
		       			}
		       			else
		       			{
		       				//thua cap thi cho lai bon dang sau
		       				Double capLeft = capSol.get(i).get(j1)/(idealNodeLoad) - cap_j ;
		       				if (capLeft>0)
		       				{
			       				idCapLst.add(p.get(j1));		       						       				
		       					avaiCapLst.add(capLeft.intValue());
		       				}
		       				break;
		       			}
		       		}
	       		}
	       		
	       		funLoc.add(locF);
	       		
	       	}
	       	//ket qua o sol and funcLoc
	       	maxLinkLoad = 0.0;
	       	maxNodeLoad = 0.0;
	       	ArrayList<ArrayList<Integer>> usedBand = new ArrayList<>();
	       	ArrayList<Integer> usedReq = new ArrayList<>();
	       	for(int i=0;i<g.V();i++)
	       	{
	       		usedReq.add(0);
	       		ArrayList<Integer> te= new ArrayList<>();
	       		for(int j=0;j<g.V();j++)
	       		{
	       			te.add(0);
	       		}
	       		usedBand.add(te);
	       	}
	       	for(int i=0;i<demandArray.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size()-1;j++)
	       		{
	       			int _usedW = usedBand.get(sol.get(i).get(j)-1).get(sol.get(i).get(j+1)-1)+demandArray.get(i).bwS();
	       			usedBand.get(sol.get(i).get(j)-1).set(sol.get(i).get(j+1)-1, _usedW);
	       		}
	       		Function[] fArr = demandArray.get(i).getFunctions();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			int node = funLoc.get(i)[j];	       			
	       			int _usedReq = usedReq.get(node-1) + fArr[j].getReq();
	       			usedReq.set(node-1, _usedReq);
	       		}
	       	}
	       	for(int i=0;i<g.V();i++)
	       	{
	       		for(int j=0;j<g.V();j++)
	       		{
	       			double linkLoad = usedBand.get(i).get(j)*1.0/g.getEdgeWeight(i+1, j+1);
	       			if(linkLoad>maxLinkLoad)
	       				maxLinkLoad = linkLoad;
	       		}
	       		double nodeLoad = usedReq.get(i)*1.0/g.getCap(i+1);
	       		if(nodeLoad>maxNodeLoad)
	       			maxNodeLoad = nodeLoad;
	       	}
	       	
	       	
	       	out.write("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	out.newLine();
	       	for(int i=0;i<demandArray.size();i++)
	       	{
	       		out.write("Demand "+ demandArray.get(i).idS()+":");
	       		out.newLine();
	       		out.write("Path:");
	       		out.newLine();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			out.write(sol.get(i).get(j)+ " ");
	       		}
	       		out.newLine();
	       		out.write("Function Location: ");
	       		out.newLine();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			out.write(funLoc.get(i)[j]+" ");
	       		}
	       		out.newLine();
	       	}
	       	
	       	
	       	
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	}
	//Heuristic new 26Jun2017
	
	public static ArrayList<Integer> SP_unequalCost(int src, int dest, MyGraph _g,int bw,double _al,double _be)
	{
		//maximumLink=1;
		//maximumNode=1;
		ArrayList<Integer> temp = new ArrayList<>();
		SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class);
		
		//DirectedGraph<String, DefaultEdge> g_i = new DefaultDirectedGraph<>(DefaultEdge.class);
		List<String> vertexList = new ArrayList<String>();
		for (int i = 0; i < _g.V(); i++) {
				int s= i+1;
				vertexList.add("node"+s);
				g_i.addVertex("node"+s);
		}
		for(int i=0;i<_g.V();i++)
		{
			for(int j=0;j<_g.V();j++)
			{
				if(i!=j && _g.getEdgeWeight(i+1, j+1)>=bw)
				{
					if(i!=src-1 || j!=dest-1)
					{				
						DefaultWeightedEdge e=g_i.addEdge(vertexList.get(i), vertexList.get(j));   
						double w = maximumLink*_al/_g.getEdgeWeight(i+1, j+1)+_be*maximumNode/_g.getCap(j+1);
						g_i.setEdgeWeight(e, w);
					}
					else
					{
						DefaultWeightedEdge e=g_i.addEdge(vertexList.get(i), vertexList.get(j));   
						double w = 100;
						g_i.setEdgeWeight(e, w);
					}
				}
			}
		}
		List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, vertexList.get(src-1),vertexList.get(dest-1));
		if(_p!=null && _p.size()>0)
		{
			for(DefaultWeightedEdge e: _p)
			{
				int int_s =Integer.parseInt(g_i.getEdgeSource(e).replaceAll("[\\D]", ""));
				temp.add(int_s);
			}
			temp.add(dest);		
		}
		
		return temp;
	}
	
	public static ArrayList<Integer> SP(int src, int dest, MyGraph _g,int bw)
	{
		//maximumLink=1;
		//maximumNode=1;
		ArrayList<Integer> temp = new ArrayList<>();
		SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class);
		
		//DirectedGraph<String, DefaultEdge> g_i = new DefaultDirectedGraph<>(DefaultEdge.class);
		List<String> vertexList = new ArrayList<String>();
		for (int i = 0; i < _g.V(); i++) {
				int s= i+1;
				vertexList.add("node"+s);
				g_i.addVertex("node"+s);
		}
		for(int i=0;i<_g.V();i++)
		{
			for(int j=0;j<_g.V();j++)
			{
				if(i!=j && _g.getEdgeWeight(i+1, j+1)>=bw)
				{				
						DefaultWeightedEdge e=g_i.addEdge(vertexList.get(i), vertexList.get(j));   
						double w = _g.getEdgeWeight(i+1, j+1);
						g_i.setEdgeWeight(e, w);
				}
			}
		}
		List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, vertexList.get(src-1),vertexList.get(dest-1));
		if(_p!=null && _p.size()>0)
		{
			for(DefaultWeightedEdge e: _p)
			{
				int int_s =Integer.parseInt(g_i.getEdgeSource(e).replaceAll("[\\D]", ""));
				temp.add(int_s);
			}
			temp.add(dest);		
		}
		
		return temp;
	}
	
	
	public static ArrayList<Demand> sortDemandIncreasingSize(ArrayList<Demand> dLst, ArrayList<Integer> sz, ArrayList<ArrayList<Integer>> _sol)
	{
		ArrayList<Demand> dLstFinal = new ArrayList<>();
		ArrayList<ArrayList<Integer>> temp = new ArrayList<>();
		int l=sz.size();
		while(l>0)
		{
			int max = Integer.MAX_VALUE;
			int max_id = -1;
			for(int i=0;i<sz.size();i++)
			{
				if(sz.get(i)<max)
				{
					max = sz.get(i);
					max_id=i;					
				}
			}
			if(max_id ==-1)
				break;
			dLstFinal.add(dLst.get(max_id));
			temp.add(_sol.get(max_id));
			sz.set(max_id, Integer.MAX_VALUE);
		}
		for(int i=0;i<_sol.size();i++)
			_sol.set(i, temp.get(i));
		return dLstFinal;		
	
	
	}
	
	public static ArrayList<Demand> sortDemandDecreasingSize(ArrayList<Demand> dLst, ArrayList<Integer> sz, ArrayList<ArrayList<Integer>> _sol)
	{

		ArrayList<Demand> dLstFinal = new ArrayList<>();
		ArrayList<ArrayList<Integer>> temp = new ArrayList<>();
		int l=sz.size();
		while(l>0)
		{
			int max = -1;
			int max_id = -1;
			for(int i=0;i<sz.size();i++)
			{
				if(sz.get(i)>max)
				{
					max = sz.get(i);
					max_id=i;					
				}
			}
			if(max_id ==-1)
				break;
			dLstFinal.add(dLst.get(max_id));
			temp.add(_sol.get(max_id));
			sz.set(max_id, -1);
		}
		for(int i=0;i<_sol.size();i++)
			_sol.set(i, temp.get(i));
		return dLstFinal;		
	
	}
	
	public static ArrayList<Demand> sortDemand(ArrayList<Demand> dLst)
	{
		ArrayList<Demand> dLstFinal = new ArrayList<>();
		ArrayList<Demand> temp = new  ArrayList<>();
		for(int i=0;i<dLst.size();i++)
		{
			Demand _d = dLst.get(i);
			temp.add(_d);
		}
		int l=temp.size();
		while(l>0)
		{
			int max_bw = -1;
			int max_id = -1;
			for(int i=0;i<temp.size();i++)
			{
				if(temp.get(i).bwS()>max_bw)
				{
					max_bw = temp.get(i).bwS();
					max_id=i;					
				}
			}
			dLstFinal.add(temp.get(max_id));
			temp.remove(max_id);
			l= temp.size();
		}
		return dLstFinal;
		
	}
	
	public static ArrayList<Integer> maxCapPath(int source, int destination, MyGraph _g,double bw)
	{
		int _v= _g.V();
		ArrayList<ArrayList<Integer>> _shortestPathLst = new ArrayList<>();
		ArrayList<Integer> _shortestPath = new ArrayList<>();
		DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> g_i = new DefaultDirectedWeightedGraph<>(DefaultWeightedEdge.class);
		List<Vertex> vertexList = new ArrayList<Vertex>();
		for (int i = 0; i < _v; i++) 
		{
			int s= i+1;
			Vertex v = new Vertex(s);
			vertexList.add(v);
			g_i.addVertex(v);
		}
		for (int j1=0;j1<_v;j1++)
			for(int j2=0;j2<_v;j2++)
			{
				if((j1!=j2) && (_g.getEdgeWeight(j1+1, j2+1)>=bw))
				{
					Vertex v1 = vertexList.get(j1);
					Vertex v2 = vertexList.get(j2);
					DefaultWeightedEdge e = g_i.addEdge(v1, v2);
					//g_i.setEdgeWeight(e,_g.getEdgeWeight(j1+1, j2+1)/(_g.getCap(j2+1)+1));
					g_i.setEdgeWeight(e,_g.getEdgeWeight(j1+1, j2+1)*(_g.getCap(j2+1)+1)/maximumNode);
				}
			}
		//System.out.println("src: "+ src);
		modifiedDijkstra d = new modifiedDijkstra(g_i);
		
		d.computeAllShortestPaths(source);
		//Collection<Vertex> vertices = g_i.getVertices();
		Vertex v= vertexList.get(0);
		for (Vertex ve:vertexList)
		{
			if (ve.getId()==destination)
			{
				v=ve;
				break;
			}
		}
		int i = 1;
			List<Vertex> _sp = d.getShortestPathTo(v);	
			_shortestPath = new ArrayList<>();
			if(_sp!=null && _sp.get(0).getId()==source)
			{
				
				for (Vertex v1:_sp)
				{
					_shortestPath.add(v1.getId());
				}
				//System.out.println("Path " + i + ": " + p);
			}
//		Set<List<Vertex>> allShortestPaths = d.getAllShortestPathsTo(v);
// 
//		for (Iterator<List<Vertex>> iter = allShortestPaths.iterator(); iter.hasNext(); i++)
//		{
//			check=false;
//			_shortestPath = new ArrayList<>();
//			List<Vertex> p = (List<Vertex>) iter.next();
//			if(!check && p.get(0).getId()==source)
//			{
//				
//				for (Vertex v1:p)
//				{
//					_shortestPath.add(v1.getId());
//				}
//				_shortestPathLst.add(_shortestPath);
//				//System.out.println("Path " + i + ": " + p);
//			}
//		}
		
		if(_shortestPath.size()==0)
			return null;

		return _shortestPath;
	
	}
	public static ArrayList<Integer> NodePlacement(Demand _d, ArrayList<Integer> p, MyGraph _g)
	{
		ArrayList<Integer> N_q= new ArrayList<>();
		Function[] fArr = _d.getFunctions();
		ArrayList<Integer> cap_p = new ArrayList<>();
		for(int i=0;i<p.size();i++)
		{
			cap_p.add(_g.getCap(p.get(i)));
		}
		int dem=0;
		for(int i=0;i<fArr.length;i++)
		{
			Function _f = fArr[i];
			for(int j=dem;j<p.size();j++)
			{
				//tim node dau tien thoa man de dat function thu i
				if(cap_p.get(j)>_f.getReq())
				{
					N_q.add(p.get(j));
					cap_p.set(j, cap_p.get(j)-_f.getReq());
					dem=j;
					break;
				}
			}
		}
		if(N_q.size()!= fArr.length)// solution not found
			return null;
		int ed = p.size();
		for(int i=fArr.length-1;i>0;i--)
		{
			Function _f = fArr[i];
			int st = p.indexOf( N_q.get(i));	
			int min=-1;
			int id_min =-1;
			for(int j=st;j<ed;j++)
			{
				if(min==-1||min<cap_p.get(j))
				{
					min = cap_p.get(j);
					id_min= j;
				}
			}
			cap_p.set(st, cap_p.get(st)+_f.getReq());
			
			N_q.set(i, p.get(id_min));
			cap_p.set(id_min, cap_p.get(id_min)-_f.getReq());
			ed=id_min+1;
		}
		return N_q;
	}
	public static void Heuristic(ArrayList<Demand> _dSet, MyGraph _gg)//Heuristic at 27-08-2017
	{

		int accept_No=_dSet.size();	
	      MyGraph g_edit = new MyGraph(_gg.K, _gg.w);	
	      MyGraph g_save = new MyGraph(_gg.K, _gg.w);
	  	ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	
	       	//Tim duong di cho tung demand dua vao tai hien tai
			
			ArrayList<Demand> dLst = sortDemand(_dSet);
	       	//ArrayList<Demand> dLst = demandArray;
	       	//ArrayList<Demand> dLst = sortDemandIncreasing(demandArray);
			boolean _block = false;
			ArrayList<Demand> dAcc= new ArrayList<>();
			
			for(int i=0;i<dLst.size();i++)
			{
				g_save= new MyGraph(g_edit.K, g_edit.w);
				_block= false;
				int _count=0;
		       	for (int i1=0;i1<g_edit.V();i1++)
		       	{
		       		if(g_edit.getCap(i1+1)>0)
		       		{
		       			maximumNode+= g_edit.getCap(i1+1)*g_edit.getCap(i1+1);
		       			_count++;
		       		}
		       	}
		       	maximumNode= Math.sqrt(maximumNode)/_count;
				
				Demand _d = dLst.get(i);
				int src=_d.sourceS();
				int dest = _d.destinationS();
				ArrayList<Integer> p= maxCapPath(src, dest, g_edit, _d.bwS());
				if(p==null || p.size()==0)
				{
					System.out.println("Path routing violation: "+ src + ","+ dest);
					g_edit = new MyGraph(g_save.K, g_save.w);
					accept_No--;
	       			_block = true;
	       			continue;
				}
				int sum_req=0;
				Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	
	       		int tb_req = sum_req/p.size();
				if(p!=null)
				{
					
					for(int j=0;j<p.size()-1;j++)
					{
						int w = g_edit.getEdgeWeight(p.get(j), p.get(j+1))-_d.bwS();
						g_edit.setEdgeWeight(p.get(j), p.get(j+1), w);
						g_edit.setCap(p.get(j), g_edit.getCap(p.get(j))-tb_req);
					}
					g_edit.setCap(p.get(p.size()-1), g_edit.getCap(p.get(p.size()-1))-tb_req);
					
					
					//dat function
					
		       		ArrayList<Integer> locF = new ArrayList<>();
		       		locF = NodePlacement(dLst.get(i), p, g_edit); 
		       		if(locF==null || locF.size()==0)
		       		{
		       			System.out.println("Function placement violation- Block");
		       			g_edit = new MyGraph(g_save.K, g_save.w);
		       			_block = true;
		       			accept_No--;
		       			continue;
		       		
		       		}
		       		for(int j=0;j<locF.size();j++)
		       		{
		       			int v= locF.get(j);
		       			int cap_v = g_edit.getCap(v) - fArr[j].getReq();
		       			g_edit.setCap(v, cap_v);
		       		}
		       		funLoc.add(locF);
		       		sol.add(p);
		       		dAcc.add(_d);
				}
				
			}
			
			_solSet = new solSet(dAcc, sol, funLoc, dLst.size()-accept_No);
			
//			g_edit = new MyGraph(g.K, g.w);	
//			ArrayList<Integer> sz = new ArrayList<>();
//			for(int i=0;i<sol.size();i++)
//				sz.add(sol.get(i).size());
//	      //place function + update resource
//			dLst = sortDemandIncreasingSize(dLst, sz, sol);
//	       
//	       	for(int i=0;i<sol.size();i++)
//	       	{
//	       		//for each demand
//	       		ArrayList<Integer> p = sol.get(i);
//	       		Function[] fArr = dLst.get(i).getFunctions();
//	       		ArrayList<Integer> locF = new ArrayList<>();
//	       		locF = NodePlacement(dLst.get(i), p, g_edit); 
//	       		if(locF==null || locF.size()==0)
//	       		{
//	       			System.out.println("Function placement violation- Block");
//	       			
//	       			_block = true;
//	       			return;
//	       		}
//	       		for(int j=0;j<locF.size();j++)
//	       		{
//	       			int v= locF.get(j);
//	       			int cap_v = g_edit.getCap(v) - fArr[j].getReq();
//	       			g_edit.setCap(v, cap_v);
//	       		}
//	       		funLoc.add(locF);
//	       		
//	       	}
	       	
	       	//ket qua o sol and funcLoc
	       	maxLinkLoad = 0.0;
	       	maxNodeLoad = 0.0;
	       	ArrayList<ArrayList<Integer>> usedBand = new ArrayList<>();
	       	ArrayList<Integer> usedReq = new ArrayList<>();
	       	for(int i=0;i<_gg.V();i++)
	       	{
	       		usedReq.add(0);
	       		ArrayList<Integer> te= new ArrayList<>();
	       		for(int j=0;j<_gg.V();j++)
	       		{
	       			te.add(0);
	       		}
	       		usedBand.add(te);
	       	}
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size()-1;j++)
	       		{
	       			int _usedW = usedBand.get(sol.get(i).get(j)-1).get(sol.get(i).get(j+1)-1)+dLst.get(i).bwS();
	       			usedBand.get(sol.get(i).get(j)-1).set(sol.get(i).get(j+1)-1, _usedW);
	       		}
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<funLoc.get(i).size();j++)
	       		{
	       			int node = funLoc.get(i).get(j);	       			
	       			int _usedReq = usedReq.get(node-1) + fArr[j].getReq();
	       			usedReq.set(node-1, _usedReq);
	       		}
	       	}
	       	for(int i=0;i<_gg.V();i++)
	       	{
	       		for(int j=0;j<_gg.V();j++)
	       		{
	       			double linkLoad = usedBand.get(i).get(j)*1.0/_gg.getEdgeWeight(i+1, j+1);
	       			if(linkLoad>maxLinkLoad)
	       				maxLinkLoad = linkLoad;
	       		}
	       		double nodeLoad = usedReq.get(i)*1.0/_gg.getCap(i+1);
	       		if(nodeLoad>maxNodeLoad)
	       			maxNodeLoad = nodeLoad;
	       	}
	       
	
	}
	
	public static void Heuristic(String outFile)//Heuristic at 12-07-2017//MSTH
	{
		int spineCount =0;
		int accept_No=d;

		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	      MyGraph g_edit = new MyGraph(g.K, g.w);	
	      MyGraph g_save = new MyGraph(g.K, g.w);
	  	ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	
	       	//Tim duong di cho tung demand dua vao tai hien tai
			
			ArrayList<Demand> dLst = sortDemand(demandArray);
	       	//ArrayList<Demand> dLst = demandArray;
	       	//ArrayList<Demand> dLst = sortDemandIncreasing(demandArray);
			boolean _block = false;
			ArrayList<Demand> dAcc= new ArrayList<>();
			
			for(int i=0;i<dLst.size();i++)
			{
				g_save= new MyGraph(g_edit.K, g_edit.w);
				_block= false;
				int _count=0;
		       	for (int i1=0;i1<g_edit.V();i1++)
		       	{
		       		if(g_edit.getCap(i1+1)>0)
		       		{
		       			maximumNode+= g_edit.getCap(i1+1)*g_edit.getCap(i1+1);
		       			_count++;
		       		}
		       	}
		       	maximumNode= Math.sqrt(maximumNode)/_count;
				
				Demand _d = dLst.get(i);
				int src=_d.sourceS();
				int dest = _d.destinationS();
				ArrayList<Integer> p= maxCapPath(src, dest, g_edit, _d.bwS());
				if(p==null || p.size()==0)
				{
					g_edit = new MyGraph(g_save.K, g_save.w);
					p= SP(src, dest, g_edit, _d.bwS());
					if(p==null || p.size()==0)
					{
						System.out.println("Path routing violation: "+ src + ","+ dest);
						g_edit = new MyGraph(g_save.K, g_save.w);
						accept_No--;
		       			_block = true;
		       			continue;
					}
					
				}
				int sum_req=0;
				Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	
	       		int tb_req = sum_req/p.size();
				if(p!=null)
				{
					
					for(int j=0;j<p.size()-1;j++)
					{
						int w = g_edit.getEdgeWeight(p.get(j), p.get(j+1))-_d.bwS();
						g_edit.setEdgeWeight(p.get(j), p.get(j+1), w);
						//g_edit.setCap(p.get(j), g_edit.getCap(p.get(j))-tb_req);
					}
					//g_edit.setCap(p.get(p.size()-1), g_edit.getCap(p.get(p.size()-1))-tb_req);
					
					
					//dat function
					
		       		ArrayList<Integer> locF = new ArrayList<>();
		       		locF = NodePlacement(dLst.get(i), p, g_edit); 
		       		if(locF==null || locF.size()==0)
		       		{
		       			System.out.println("Function placement violation- Block");
		       			g_edit = new MyGraph(g_save.K, g_save.w);
		       			_block = true;
		       			accept_No--;
		       			continue;
		       		
		       		}
		       		for(int j=0;j<locF.size();j++)
		       		{
		       			int v= locF.get(j);
		       			int cap_v = g_edit.getCap(v) - fArr[j].getReq();
		       			g_edit.setCap(v, cap_v);
		       		}
		       		funLoc.add(locF);
		       		sol.add(p);
		       		dAcc.add(_d);
				}
				
			}
			
			_solSet = new solSet(dAcc, sol, funLoc, dLst.size()-accept_No);
			
//			g_edit = new MyGraph(g.K, g.w);	
//			ArrayList<Integer> sz = new ArrayList<>();
//			for(int i=0;i<sol.size();i++)
//				sz.add(sol.get(i).size());
//	      //place function + update resource
//			dLst = sortDemandIncreasingSize(dLst, sz, sol);
//	       
//	       	for(int i=0;i<sol.size();i++)
//	       	{
//	       		//for each demand
//	       		ArrayList<Integer> p = sol.get(i);
//	       		Function[] fArr = dLst.get(i).getFunctions();
//	       		ArrayList<Integer> locF = new ArrayList<>();
//	       		locF = NodePlacement(dLst.get(i), p, g_edit); 
//	       		if(locF==null || locF.size()==0)
//	       		{
//	       			System.out.println("Function placement violation- Block");
//	       			
//	       			_block = true;
//	       			return;
//	       		}
//	       		for(int j=0;j<locF.size();j++)
//	       		{
//	       			int v= locF.get(j);
//	       			int cap_v = g_edit.getCap(v) - fArr[j].getReq();
//	       			g_edit.setCap(v, cap_v);
//	       		}
//	       		funLoc.add(locF);
//	       		
//	       	}
	       	
	       	//ket qua o sol and funcLoc
	       	maxLinkLoad = 0.0;
	       	maxNodeLoad = 0.0;
	       	ArrayList<ArrayList<Integer>> usedBand = new ArrayList<>();
	       	ArrayList<Integer> usedReq = new ArrayList<>();
	       	for(int i=0;i<g.V();i++)
	       	{
	       		usedReq.add(0);
	       		ArrayList<Integer> te= new ArrayList<>();
	       		for(int j=0;j<g.V();j++)
	       		{
	       			te.add(0);
	       		}
	       		usedBand.add(te);
	       	}
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size()-1;j++)
	       		{
	       			int _usedW = usedBand.get(sol.get(i).get(j)-1).get(sol.get(i).get(j+1)-1)+dLst.get(i).bwS();
	       			usedBand.get(sol.get(i).get(j)-1).set(sol.get(i).get(j+1)-1, _usedW);
	       		}
	       		Function[] fArr = dAcc.get(i).getFunctions();
	       		for(int j=0;j<funLoc.get(i).size();j++)
	       		{
	       			int node = funLoc.get(i).get(j);	       			
	       			int _usedReq = usedReq.get(node-1) + fArr[j].getReq();
	       			usedReq.set(node-1, _usedReq);
	       		}
	       	}
	       	for(int i=0;i<g.V();i++)
	       	{
	       		for(int j=0;j<g.V();j++)
	       		{
	       			double linkLoad = usedBand.get(i).get(j)*1.0/g.getEdgeWeight(i+1, j+1);
	       			if(linkLoad>maxLinkLoad)
	       				maxLinkLoad = linkLoad;
	       		}
	       		double nodeLoad = usedReq.get(i)*1.0/g.getCap(i+1);
	       		if(nodeLoad>maxNodeLoad)
	       			maxNodeLoad = nodeLoad;
	       	}
	       	
	       	out.write("Accept Number: "+ accept_No);
	       	out.newLine();
	       	
	       	System.out.println("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	value_final = 10.0*accept_No/dLst.size() - maxLinkLoad-maxNodeLoad;
	       _acceptNo = accept_No*1.0;
	       	System.out.println("value: "+ value_final);
	       	out.write("Solution: "+maxLinkLoad +","+maxNodeLoad + ":::"+ value_final);
	       	out.newLine();
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		//out.write("Demand "+ dLst.get(i).idS()+":");
	       		//out.newLine();
	       		out.write("Path:");
	       		out.newLine();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			out.write(sol.get(i).get(j)+ " ");
	       		}
	       		out.newLine();
	       		out.write("Function Location: ");
	       		out.newLine();
	       		for(int j=0;j<funLoc.get(i).size();j++)
	       		{
	       			out.write(funLoc.get(i).get(j)+" ");
	       			if(g.getCap(funLoc.get(i).get(j))>leafCapacity)
	       				spineCount++;
	       				
	       		}
	       		
	       		out.newLine();
	       	}
	       	out.write("Ratio of Spine: "+ spineCount*1.0/(m1*accept_No));
	       	spineRatio = spineCount*1.0/(m1*_acceptNo);
			System.out.println("Spine Ratio = "+ spineRatio);
	       	out.newLine();
	       	
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	}
	
	public static void SimpleHeuristic(String outFile)
	{


		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	      MyGraph g_edit = new MyGraph(g.K, g.w);	
	       	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	
	       	//Tim duong di cho tung demand dua vao tai hien tai
			
			ArrayList<Demand> dLst = sortDemand(demandArray);
	       	//ArrayList<Demand> dLst = demandArray;
	       	//ArrayList<Demand> dLst = sortDemandIncreasing(demandArray);
			for(int i=0;i<dLst.size();i++)
			{
				maximumLink=0;
		       	maximumNode=0;
		       int _count = 0;
		       	for (int i1=0;i1<g_edit.V();i1++)
		       		for(int j=0;j<g_edit.V();j++)
		       		{
		       			if(g_edit.getEdgeWeight(i1+1, j+1)>0)
		       			{
		       				_count++;
		       				maximumLink += g_edit.getEdgeWeight(i1+1, j+1)*g_edit.getEdgeWeight(i1+1, j+1);
		       			}
		       		}
		       			
		       	maximumLink= Math.sqrt(maximumLink)/_count;
		       	_count=0;
		       	for (int i1=0;i1<g_edit.V();i1++)
		       	{
		       		if(g_edit.getCap(i1+1)>0)
		       		{
		       			maximumNode+= g_edit.getCap(i1+1)*g_edit.getCap(i1+1);
		       			_count++;
		       		}
		       	}
		       	maximumNode= Math.sqrt(maximumNode)/_count;
				Demand _d = dLst.get(i);
				int src=_d.sourceS();
				int dest = _d.destinationS();
				ArrayList<Integer> p= SP_unequalCost(src, dest, g_edit, _d.bwS(),0.99999,0.00001);
				if(p==null || p.size()==0)
				{
					System.out.println("Demand nay khong thoa man");
					return;
				}
				int sum_req=0;
				Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	
	       		int tb_req = sum_req/p.size();
				if(p!=null)
				{
					sol.add(p);
					for(int j=0;j<p.size()-1;j++)
					{
						int w = g_edit.getEdgeWeight(p.get(j), p.get(j+1))-_d.bwS();
						g_edit.setEdgeWeight(p.get(j), p.get(j+1), w);
						g_edit.setCap(p.get(j), g_edit.getCap(p.get(j))-tb_req);
					}
					g_edit.setCap(p.get(p.size()-1), g_edit.getCap(p.get(p.size()-1))-tb_req);
				}
				
			}
			
			g_edit = new MyGraph(g.K, g.w);	
			ArrayList<Integer> sz = new ArrayList<>();
			for(int i=0;i<sol.size();i++)
				sz.add(sol.get(i).size());
	      //place function + update resource
			dLst = sortDemandDecreasingSize(dLst, sz, sol);
	       	int sum_cap = 0;
	       	ArrayList<Integer> setNode = new ArrayList<>();
	       	ArrayList<Integer> setDiffNode = new ArrayList<>();
	       
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			
	       			setNode.add(sol.get(i).get(j));
	       			if(!setDiffNode.contains(sol.get(i).get(j)))
	       			{
	       				setDiffNode.add(sol.get(i).get(j));
	       				sum_cap+=g_edit.getCap(sol.get(i).get(j));
	       			}
	       		}
	       	}
	       	
	    	ArrayList<ArrayList<Integer>> times = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			int num= numberOfTimes(sol.get(i).get(j),setNode);
	       			ti.add(num);
	       		}
	       		times.add(ti);
	       	}
	       	
	       	int sum_req = 0;
	       	for(int i=0;i<dLst.size();i++)
	       	{
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	       		
	       	}
	       	double idealNodeLoad = sum_req*1.0/sum_cap +0.01;
	       	
	       
	       	ArrayList<Integer[]> funLoc = new ArrayList<>();
	       	
	       	ArrayList<ArrayList<Integer>> capSol = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			ti.add(g_edit.getCap(sol.get(i).get(j))/times.get(i).get(j));
	       		}
	       		capSol.add(ti);
	       	}
	       	ArrayList<Integer> idCapLst = new ArrayList<>();
	       	ArrayList<Integer> avaiCapLst = new ArrayList<>();
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		//for each demand
	       		ArrayList<Integer> p = sol.get(i);
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		Integer[] locF = new Integer[fArr.length];
	       		int id=0;
	       		int jend =0;
	       		double idealPara = idealNodeLoad;
	       		boolean redo= false;
	       		for (int j1=jend;j1<p.size();j1++)
	       		{
	       			int cap_j = capSol.get(i).get(j1);
	       			if(idCapLst.contains(p.get(j1)))
	       			{
	       				int index = idCapLst.indexOf(p.get(j1));
	       				cap_j+=avaiCapLst.get(index);
	       				capSol.get(i).set(j1, cap_j);
	       				idCapLst.remove(index);
	       				avaiCapLst.remove(index);
	       			}
	       			double loaded =0.0;
	       			for(int j2=id;j2<fArr.length;j2++)
		       		{
	       				loaded+= fArr[j2].getReq()*1.0;
		       			if(loaded/cap_j<idealPara )
		       			{	      				
		       				
		       				if(cap_j-fArr[j2].getReq()>=0)
		       				{
		       					locF[j2] = p.get(j1);
		       					capSol.get(i).set(j1, cap_j-fArr[j2].getReq());	
		       					g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
		       				}
		       				else
		       				{
		       					if(g_edit.getCap(p.get(j1))>=fArr[j2].getReq())
		       					{
		       						locF[j2] = p.get(j1);
		       						capSol.get(i).set(j1, cap_j-fArr[j2].getReq());	
		       						g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
		       					}
		       					else
		       					{
		       						System.out.println("Demand nay khong thoa man");
		       						return;
		       					}
		       				}
		       				id++;
		       				jend=j1;
		       				if(id==fArr.length)
		       				{
		       					for(int j3=j1;j3<p.size();j3++)
		       					{
		       						cap_j = capSol.get(i).get(j3);
		       						idCapLst.add(p.get(j3));		       						       				
			       					avaiCapLst.add(cap_j);
		       					}
		       				}
		       			}
		       			else
		       			{
		       				if(j1==p.size()-1)
		       				{
		       					if(jend==p.size()-1)
		       					{
		       						if(cap_j-fArr[j2].getReq()>=0)
				       				{
				       					locF[j2] = p.get(j1);
				       					capSol.get(i).set(j1, cap_j-fArr[j2].getReq());	
				       					g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
				       				}
				       				else
				       				{
				       					if(g_edit.getCap(p.get(j1))>=fArr[j2].getReq())
				       					{
				       						locF[j2] = p.get(j1);
				       						capSol.get(i).set(j1, cap_j-fArr[j2].getReq());	
				       						g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
				       					}
				       					else
				       					{
				       						System.out.println("Demand nay khong thoa man");
				       						return;
				       					}
				       				}
				       				id++;
				       				jend=j1;
				       				continue;
		       					}
		       					else
		       					{
		       					//giai quyet lai neu fArr chua het, k the tong vao 1 node cuoi cung duoc.
			       					//node cuoi cung can xu ly la jEnd->het
			       					idealPara +=0.1; 
			       					for(int j3=jend;j3<p.size();j3++)
			       					{
			       						int index = idCapLst.indexOf(p.get(j3));
			       						if(index!=-1)
			       						{
				       						idCapLst.remove(index);
				    	       				avaiCapLst.remove(index);
			       						}
			       					}
			       					j1=jend;
			       					redo=true;
			       					break;
		       					}
		       					
		       				}
		       				//thua cap thi cho lai bon dang sau
		       				Double capLeft = (capSol.get(i).get(j1)+(idealNodeLoad-1)*cap_j)/(idealNodeLoad) ;
		       				if (capLeft>0)
		       				{
			       				idCapLst.add(p.get(j1));		       						       				
		       					avaiCapLst.add(capLeft.intValue());
		       				}
		       				break;
		       			}
		       		}
	       		}
	       		
	       		funLoc.add(locF);
	       		
	       	}
	       	//ket qua o sol and funcLoc
	       	maxLinkLoad = 0.0;
	       	maxNodeLoad = 0.0;
	       	ArrayList<ArrayList<Integer>> usedBand = new ArrayList<>();
	       	ArrayList<Integer> usedReq = new ArrayList<>();
	       	for(int i=0;i<g.V();i++)
	       	{
	       		usedReq.add(0);
	       		ArrayList<Integer> te= new ArrayList<>();
	       		for(int j=0;j<g.V();j++)
	       		{
	       			te.add(0);
	       		}
	       		usedBand.add(te);
	       	}
	       	for(int i=0;i<dLst.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size()-1;j++)
	       		{
	       			int _usedW = usedBand.get(sol.get(i).get(j)-1).get(sol.get(i).get(j+1)-1)+dLst.get(i).bwS();
	       			usedBand.get(sol.get(i).get(j)-1).set(sol.get(i).get(j+1)-1, _usedW);
	       		}
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			int node = funLoc.get(i)[j];	       			
	       			int _usedReq = usedReq.get(node-1) + fArr[j].getReq();
	       			usedReq.set(node-1, _usedReq);
	       		}
	       	}
	       	for(int i=0;i<g.V();i++)
	       	{
	       		for(int j=0;j<g.V();j++)
	       		{
	       			double linkLoad = usedBand.get(i).get(j)*1.0/g.getEdgeWeight(i+1, j+1);
	       			if(linkLoad>maxLinkLoad)
	       				maxLinkLoad = linkLoad;
	       		}
	       		double nodeLoad = usedReq.get(i)*1.0/g.getCap(i+1);
	       		if(nodeLoad>maxNodeLoad)
	       			maxNodeLoad = nodeLoad;
	       	}
	       	
	       	
	       	out.write("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	System.out.println("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	out.newLine();
	       	for(int i=0;i<dLst.size();i++)
	       	{
	       		out.write("Demand "+ dLst.get(i).idS()+":");
	       		out.newLine();
	       		out.write("Path:");
	       		out.newLine();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			out.write(sol.get(i).get(j)+ " ");
	       		}
	       		out.newLine();
	       		out.write("Function Location: ");
	       		out.newLine();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			out.write(funLoc.get(i)[j]+" ");
	       		}
	       		out.newLine();
	       	}
	       	
	       	
	       	
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	}
	
	public static void EditHeuristic(String outFile)
	{
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	      MyGraph g_edit = new MyGraph(g.K, g.w);	
	       	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	
	       	//Tim duong di cho tung demand dua vao tai hien tai
			
			ArrayList<Demand> dLst = sortDemand(demandArray);
	       	//ArrayList<Demand> dLst = demandArray;
	       	//ArrayList<Demand> dLst = sortDemandIncreasing(demandArray);
			for(int i=0;i<dLst.size();i++)
			{
				maximumLink=0;
		       	maximumNode=0;
		       int _count = 0;
		       	for (int i1=0;i1<g_edit.V();i1++)
		       		for(int j=0;j<g_edit.V();j++)
		       		{
		       			if(g_edit.getEdgeWeight(i1+1, j+1)>0)
		       			{
		       				_count++;
		       				maximumLink += g_edit.getEdgeWeight(i1+1, j+1)*g_edit.getEdgeWeight(i1+1, j+1);
		       			}
		       		}
		       			
		       	maximumLink= Math.sqrt(maximumLink)/_count;
		       	_count=0;
		       	for (int i1=0;i1<g_edit.V();i1++)
		       	{
		       		if(g_edit.getCap(i1+1)>0)
		       		{
		       			maximumNode+= g_edit.getCap(i1+1)*g_edit.getCap(i1+1);
		       			_count++;
		       		}
		       	}
		       	maximumNode= Math.sqrt(maximumNode)/_count;
				Demand _d = dLst.get(i);
				int src=_d.sourceS();
				int dest = _d.destinationS();
				ArrayList<Integer> p= SP_unequalCost(src, dest, g_edit, _d.bwS(),0.99999,0.00001);
				if(p==null || p.size()==0)
				{
					System.out.println("Demand nay khong thoa man");
					return;
				}
				int sum_req=0;
				Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	
	       		int tb_req = sum_req/p.size();
				if(p!=null)
				{
					sol.add(p);
					for(int j=0;j<p.size()-1;j++)
					{
						int w = g_edit.getEdgeWeight(p.get(j), p.get(j+1))-_d.bwS();
						g_edit.setEdgeWeight(p.get(j), p.get(j+1), w);
						g_edit.setCap(p.get(j), g_edit.getCap(p.get(j))-tb_req);
					}
					g_edit.setCap(p.get(p.size()-1), g_edit.getCap(p.get(p.size()-1))-tb_req);
				}
				
			}
			
			g_edit = new MyGraph(g.K, g.w);	
			ArrayList<Integer> sz = new ArrayList<>();
			for(int i=0;i<sol.size();i++)
				sz.add(sol.get(i).size());
	      //place function + update resource
			dLst = sortDemandIncreasingSize(dLst, sz, sol);
	       	int sum_cap = 0;
	       	ArrayList<Integer> setNode = new ArrayList<>();
	       	ArrayList<Integer> setDiffNode = new ArrayList<>();
	       
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			
	       			setNode.add(sol.get(i).get(j));
	       			if(!setDiffNode.contains(sol.get(i).get(j)))
	       			{
	       				setDiffNode.add(sol.get(i).get(j));
	       				sum_cap+=g_edit.getCap(sol.get(i).get(j));
	       			}
	       		}
	       	}
	       	
	    	ArrayList<ArrayList<Integer>> times = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			int num= numberOfTimes(sol.get(i).get(j),setNode);
	       			ti.add(num);
	       		}
	       		times.add(ti);
	       	}
	       	
	       	int sum_req = 0;
	       	for(int i=0;i<dLst.size();i++)
	       	{
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<fArr.length;j++)
	       			sum_req +=fArr[j].getReq();	       		
	       	}
	       	double idealNodeLoad = sum_req*1.0/sum_cap +0.01;
	       	
	       
	       	ArrayList<Integer[]> funLoc = new ArrayList<>();
	       	
	       	ArrayList<ArrayList<Integer>> capSol = new ArrayList<>();
	       	for (int i=0;i<sol.size();i++)
	       	{
	       		ArrayList<Integer> ti = new ArrayList<>();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			ti.add(g_edit.getCap(sol.get(i).get(j)));
	       		}
	       		capSol.add(ti);
	       	}
	       	ArrayList<Integer> idCapLst = new ArrayList<>();
	       	ArrayList<Integer> avaiCapLst = new ArrayList<>();
	       	for(int i=0;i<sol.size();i++)
	       	{
	       		//for each demand
	       		ArrayList<Integer> p = sol.get(i);
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		Integer[] locF = new Integer[fArr.length];
	       		int id=0;
	       		int jend =0;
	       		double idealPara = idealNodeLoad;
	       		boolean redo= false;
	       		for (int j1=jend;j1<p.size();j1++)
	       		{
	       			int cap_j = capSol.get(i).get(j1);
	       			int loaded =0;
	       			if(idCapLst.contains(p.get(j1)))
	       			{
	       				int index = idCapLst.indexOf(p.get(j1));
	       				loaded=avaiCapLst.get(index);
	       				
	       			}
	       			
	       			for(int j2=id;j2<fArr.length;j2++)
		       		{
	       				loaded+= fArr[j2].getReq()*1.0;
		       			if(loaded*1.0/cap_j<idealPara )
		       			{	      				
		       				
		       				if(cap_j-loaded>=0)
		       				{
		       					locF[j2] = p.get(j1);
		       					capSol.get(i).set(j1, cap_j-loaded);	
		       					g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
		       					int index = idCapLst.indexOf(p.get(j1));
		       					if(index!=-1)
		       					{
		       						avaiCapLst.set(index, avaiCapLst.get(index)+fArr[j2].getReq());
		       					}
		       					else
		       					{
		       						idCapLst.add(p.get(j1));		       						       				
		       						avaiCapLst.add(fArr[j2].getReq());
		       					}
		       				}
		       				else
		       				{
		       					if(g_edit.getCap(p.get(j1))>=fArr[j2].getReq())
		       					{
		       						locF[j2] = p.get(j1);
		       						capSol.get(i).set(j1, cap_j-loaded);	
		       						g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
		       						int index = idCapLst.indexOf(p.get(j1));
			       					if(index!=-1)
			       					{
			       						avaiCapLst.set(index, avaiCapLst.get(index)+fArr[j2].getReq());
			       					}
			       					else
			       					{
			       						idCapLst.add(p.get(j1));		       						       				
			       						avaiCapLst.add(fArr[j2].getReq());
			       					}
		       					}
		       					else
		       					{
		       						System.out.println("Demand nay khong thoa man");
		       						return;
		       					}
		       				}
		       				id++;
		       				jend=j1;
		       			}
		       			else
		       			{
		       				loaded-= fArr[j2].getReq()*1.0;
		       				if(j1==p.size()-1)
		       				{
		       						loaded+= fArr[j2].getReq()*1.0;
		       						if(cap_j-loaded>=0)
				       				{
				       					locF[j2] = p.get(j1);
				       					capSol.get(i).set(j1, cap_j-loaded);	
				       					g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
				       					int index = idCapLst.indexOf(p.get(j1));
				       					if(index!=-1)
				       					{
				       						avaiCapLst.set(index, avaiCapLst.get(index)+fArr[j2].getReq());
				       					}
				       					else
				       					{
				       						idCapLst.add(p.get(j1));		       						       				
				       						avaiCapLst.add(fArr[j2].getReq());
				       					}
				       				}
				       				else
				       				{
				       					if(g_edit.getCap(p.get(j1))>=fArr[j2].getReq())
				       					{
				       						locF[j2] = p.get(j1);
				       						capSol.get(i).set(j1, cap_j-loaded);	
				       						g_edit.setCap(p.get(j1), g_edit.getCap(p.get(j1))-fArr[j2].getReq());
				       						int index = idCapLst.indexOf(p.get(j1));
					       					if(index!=-1)
					       					{
					       						avaiCapLst.set(index, avaiCapLst.get(index)+fArr[j2].getReq());
					       					}
					       					else
					       					{
					       						idCapLst.add(p.get(j1));		       						       				
					       						avaiCapLst.add(fArr[j2].getReq());
					       					}
				       					}
				       					else
				       					{
				       						System.out.println("Demand nay khong thoa man");
				       						return;
				       					}
				       				}
				       				id++;
				       				jend=j1;
				       				continue;
		       					
		       				}
		       				//thua cap thi cho lai bon dang sau
//		       				int usedCap = loaded;
//		       				if (usedCap>0)
//		       				{
//		       					int index = idCapLst.indexOf(p.get(j1));
//		       					if(index!=-1)
//		       					{
//		       						avaiCapLst.set(index, usedCap);
//		       					}
//		       					else
//		       					{
//		       						idCapLst.add(p.get(j1));		       						       				
//		       						avaiCapLst.add(usedCap);
//		       					}
//		       				}
		       				break;
		       			}
		       		}
	       		}
	       		
	       		funLoc.add(locF);
	       		
	       	}
	       	//ket qua o sol and funcLoc
	       	maxLinkLoad = 0.0;
	       	maxNodeLoad = 0.0;
	       	ArrayList<ArrayList<Integer>> usedBand = new ArrayList<>();
	       	ArrayList<Integer> usedReq = new ArrayList<>();
	       	for(int i=0;i<g.V();i++)
	       	{
	       		usedReq.add(0);
	       		ArrayList<Integer> te= new ArrayList<>();
	       		for(int j=0;j<g.V();j++)
	       		{
	       			te.add(0);
	       		}
	       		usedBand.add(te);
	       	}
	       	for(int i=0;i<dLst.size();i++)
	       	{
	       		for(int j=0;j<sol.get(i).size()-1;j++)
	       		{
	       			int _usedW = usedBand.get(sol.get(i).get(j)-1).get(sol.get(i).get(j+1)-1)+dLst.get(i).bwS();
	       			usedBand.get(sol.get(i).get(j)-1).set(sol.get(i).get(j+1)-1, _usedW);
	       		}
	       		Function[] fArr = dLst.get(i).getFunctions();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			int node = funLoc.get(i)[j];	       			
	       			int _usedReq = usedReq.get(node-1) + fArr[j].getReq();
	       			usedReq.set(node-1, _usedReq);
	       		}
	       	}
	       	for(int i=0;i<g.V();i++)
	       	{
	       		for(int j=0;j<g.V();j++)
	       		{
	       			double linkLoad = usedBand.get(i).get(j)*1.0/g.getEdgeWeight(i+1, j+1);
	       			if(linkLoad>maxLinkLoad)
	       				maxLinkLoad = linkLoad;
	       		}
	       		double nodeLoad = usedReq.get(i)*1.0/g.getCap(i+1);
	       		if(nodeLoad>maxNodeLoad)
	       			maxNodeLoad = nodeLoad;
	       	}
	       	
	       	
	       	out.write("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	System.out.println("Solution: "+maxLinkLoad +","+maxNodeLoad);
	       	out.newLine();
	       	for(int i=0;i<dLst.size();i++)
	       	{
	       		out.write("Demand "+ dLst.get(i).idS()+":");
	       		out.newLine();
	       		out.write("Path:");
	       		out.newLine();
	       		for(int j=0;j<sol.get(i).size();j++)
	       		{
	       			out.write(sol.get(i).get(j)+ " ");
	       		}
	       		out.newLine();
	       		out.write("Function Location: ");
	       		out.newLine();
	       		for(int j=0;j<funLoc.get(i).length;j++)
	       		{
	       			out.write(funLoc.get(i)[j]+" ");
	       		}
	       		out.newLine();
	       	}
	       	
	       	
	       	
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	}
	 public static int[] sortDecreasingFractional(double[] srcLst)
	  {

		  int[] temp= new int[srcLst.length];
			int dem=0;
			double[] savelst = new double[srcLst.length];
			for(int i=0;i<srcLst.length;i++)
				savelst[i]=srcLst[i];
			System.out.println("length "+ srcLst.length);
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
				System.out.println("chua xong: "+ dem);
			}
			return temp;
		
		  
	  
	  }
	 
	 public static class ArrayIndexComparator implements Comparator<Integer>
	 {
	     private final double[] array;

	     public ArrayIndexComparator(double[] array)
	     {
	         this.array = array;
	     }

	     public Integer[] createIndexArray()
	     {
	         Integer[] indexes = new Integer[array.length];
	         for (int i = 0; i < array.length; i++)
	         {
	             indexes[i] = i; // Autoboxing
	         }
	         return indexes;
	     }

	     @Override
	     public int compare(Integer index1, Integer index2)
	     {
	          // Autounbox from Integer to int to use as array indexes
	    	 if(array[index1]>array[index2])
	    		 return -1;
	    	 else
	    	 {
	    		 if(array[index1]==array[index2])
	    			 return 0;
	    		 else
	    			 return 1;
	    	 }
	     }
	 }
	 
	public static void basedHeuristic (String outFile,int p,double alpha)
	{


		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.000000001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				//model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
	//variable declaire
				
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = demandArray.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
				
			
				
				// Optimize model
				try {
					
					//int p = 100;
					//double alpha = 0.9;
					ArrayList<Integer> zeroSet = new ArrayList<>();
					ArrayList<Integer> oneSet = new ArrayList<>();
					//GRBVar[] vars = model.getVars();
					//int length = model.getVars().length;
					ArrayList<GRBVar> varsArr = new ArrayList<>();
					
					int dem=0;
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								dem++;
								varsArr.add( x1[i][k][j]);
								
							}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				varsArr.add(y1[i][j1][j2]);
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
											varsArr.add(phi[i][k][j1][j2]);
									//}
								}
					dem=0;
					GRBVar[] vars = new GRBVar[varsArr.size()];
					for(GRBVar v: varsArr)
						vars[dem++]= v;
						//set x1, y1, phi ro rang
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								x1[i][k][j].set(GRB.CharAttr.VType, 'C');
							}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'C');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					while(true)
					{
						int count = 0;
						model.update();
						model.optimize();
						
						
						//sua lai doan nay// lay nhung bien khac voi trong setzero and setone
						
						varsArr = new ArrayList<>();
						
						dem=0;
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
								{
									dem++;
									varsArr.add( x1[i][k][j]);
									
								}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
						    			//{
						    				varsArr.add(y1[i][j1][j2]);
						    			//}
						    		}
						
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
									{
										//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
											//if(j1!=j2)
										//{
												varsArr.add(phi[i][k][j1][j2]);
										//}
									}
						dem=0;
						vars = new GRBVar[varsArr.size()];
						for(GRBVar v: varsArr)
							vars[dem++]= v;
						
						
						double[] val_vars= new double[vars.length];
						for(int i=0;i<vars.length;i++)
						{
							if(vars[i].get(GRB.DoubleAttr.X)>=0.5)
								val_vars[i] = vars[i].get(GRB.DoubleAttr.X)-0.5;
							else
								val_vars[i] = -vars[i].get(GRB.DoubleAttr.X)+0.5;
						}
						ArrayIndexComparator comparator = new ArrayIndexComparator(val_vars);
						Integer[] idVars = comparator.createIndexArray();
						Arrays.sort(idVars, comparator);
						dem =0;
						while (count<p)
						{
							if(!oneSet.contains(idVars[dem]) && !zeroSet.contains(idVars[dem]))
							{

								if(val_vars[idVars[dem]]>=0.5)
								{
									count++;
									if(vars[idVars[dem]].get(GRB.DoubleAttr.X)==0.0)
									{
										zeroSet.add(idVars[dem]);
										int index= idVars[dem];
										if(index<m1*n*demandArray.size())
										{
											int j= index%n;
											int temp= index/n;
											int k = temp%m1;
											int i = temp/m1;
											x1[i][k][j].set(GRB.DoubleAttr.LB, 0);
											x1[i][k][j].set(GRB.DoubleAttr.UB, 0);
											//vars[idVars[dem]].set(GRB.DoubleAttr.LB, 0);
											//vars[idVars[dem]].set(GRB.DoubleAttr.UB, 0);
										}
										else
										{
											
											if(index<m1*n*demandArray.size()+n*n*demandArray.size() )
											{
												index = index-m1*n*demandArray.size();
												int j2= index%n;
												int temp= index/n;
												int j1 = temp%n;
												int i = temp/n;
												y1[i][j1][j2].set(GRB.DoubleAttr.LB, 0);
												y1[i][j1][j2].set(GRB.DoubleAttr.UB, 0);
												
											}
											else
											{
												index= index-m1*n*demandArray.size()-n*n*demandArray.size();
												int j2= index%n;
												int temp1= index/n;
												int j1 = temp1%n;
												int temp2 = temp1/n;
												int k= temp2%m1;
												int i=temp2/m1;
												phi[i][k][j1][j2].set(GRB.DoubleAttr.LB, 0);
												phi[i][k][j1][j2].set(GRB.DoubleAttr.UB, 0);
											}
										}
										
										
										
									}
									else
									{
										
										oneSet.add(idVars[dem]);
										int index= idVars[dem];
										if(index<m1*n*demandArray.size())
										{
											int j= index%n;
											int temp= index/n;
											int k = temp%m1;
											int i = temp/m1;
											x1[i][k][j].set(GRB.DoubleAttr.LB, 1);
											x1[i][k][j].set(GRB.DoubleAttr.UB, 1);
										}
										else
										{
											
											if(index<m1*n*demandArray.size()+n*n*demandArray.size() )
											{
												index = index-m1*n*demandArray.size();
												int j2= index%n;
												int temp= index/n;
												int j1 = temp%n;
												int i = temp/n;
												y1[i][j1][j2].set(GRB.DoubleAttr.LB, 1);
												y1[i][j1][j2].set(GRB.DoubleAttr.UB, 1);
												
											}
											else
											{
												index= index-m1*n*demandArray.size()-n*n*demandArray.size();
												int j2= index%n;
												int temp1= index/n;
												int j1 = temp1%n;
												int temp2 = temp1/n;
												int k= temp2%m1;
												int i=temp2/m1;
												phi[i][k][j1][j2].set(GRB.DoubleAttr.LB, 1);
												phi[i][k][j1][j2].set(GRB.DoubleAttr.UB, 1);
											}
										}
										
									}
								}
								else
								{
									count++;
									if(vars[idVars[dem]].get(GRB.DoubleAttr.X)<0.5)
									{
										zeroSet.add(idVars[dem]);
										int index= idVars[dem];
										if(index<m1*n*demandArray.size())
										{
											int j= index%n;
											int temp= index/n;
											int k = temp%m1;
											int i = temp/m1;
											x1[i][k][j].set(GRB.DoubleAttr.LB, 0);
											x1[i][k][j].set(GRB.DoubleAttr.UB, 0);
											//vars[idVars[dem]].set(GRB.DoubleAttr.LB, 0);
											//vars[idVars[dem]].set(GRB.DoubleAttr.UB, 0);
										}
										else
										{
											
											if(index<m1*n*demandArray.size()+n*n*demandArray.size() )
											{
												index = index-m1*n*demandArray.size();
												int j2= index%n;
												int temp= index/n;
												int j1 = temp%n;
												int i = temp/n;
												y1[i][j1][j2].set(GRB.DoubleAttr.LB, 0);
												y1[i][j1][j2].set(GRB.DoubleAttr.UB, 0);
												
											}
											else
											{
												index= index-m1*n*demandArray.size()-n*n*demandArray.size();
												int j2= index%n;
												int temp1= index/n;
												int j1 = temp1%n;
												int temp2 = temp1/n;
												int k= temp2%m1;
												int i=temp2/m1;
												phi[i][k][j1][j2].set(GRB.DoubleAttr.LB, 0);
												phi[i][k][j1][j2].set(GRB.DoubleAttr.UB, 0);
											}
										}
									}
									else
									{
										oneSet.add(idVars[dem]);
										int index= idVars[dem];
										if(index<m1*n*demandArray.size())
										{
											int j= index%n;
											int temp= index/n;
											int k = temp%m1;
											int i = temp/m1;
											x1[i][k][j].set(GRB.DoubleAttr.LB, 1);
											x1[i][k][j].set(GRB.DoubleAttr.UB, 1);
										}
										else
										{
											
											if(index<m1*n*demandArray.size()+n*n*demandArray.size() )
											{
												index = index-m1*n*demandArray.size();
												int j2= index%n;
												int temp= index/n;
												int j1 = temp%n;
												int i = temp/n;
												y1[i][j1][j2].set(GRB.DoubleAttr.LB, 1);
												y1[i][j1][j2].set(GRB.DoubleAttr.UB, 1);
												
											}
											else
											{
												index= index-m1*n*demandArray.size()-n*n*demandArray.size();
												int j2= index%n;
												int temp1= index/n;
												int j1 = temp1%n;
												int temp2 = temp1/n;
												int k= temp2%m1;
												int i=temp2/m1;
												phi[i][k][j1][j2].set(GRB.DoubleAttr.LB, 1);
												phi[i][k][j1][j2].set(GRB.DoubleAttr.UB, 1);
											}
										}
									}
								}
							}
							dem++;
							
						}
						
						if(zeroSet.size()+oneSet.size()>= alpha * vars.length)
							break;
					}
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								x1[i][k][j].set(GRB.CharAttr.VType, 'B');
							}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'B');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
									//}
								}
					model.update();
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	}
	
	public static void Cover(String outFile)
	{

		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.000000001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if(g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								if(j1!=j2)
								{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				obj.addTerm(1, r);

				model.setObjective(obj,GRB.MINIMIZE);		
				//add constraints
				GRBLinExpr ex= new GRBLinExpr();
				ex.addTerm(1,r_l);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
				
				ex= new GRBLinExpr();
				ex.addTerm(1,r_n);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						int id = getDemand(i+1).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							model.addConstr(expr3, GRB.EQUAL, 1, st);
						}
						else
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								model.addConstr(expr7, GRB.EQUAL, 1, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								model.addConstr(expr7, GRB.EQUAL, -1, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
									model.addConstr(exp, GRB.EQUAL, -1, st);
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
//							}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
			
				System.gc();
				
			
				
				// Optimize model
				try {
					//model.getEnv().set(GRB.DoubleParam.NodeLimit, 1500);
//					GRBModel m_relax = model.relax();
//					m_relax.optimize();
//					GRBVar[] n_vars = m_relax.getVars();
//					for(GRBVar vars: n_vars)
//	            	{						
//	            		double roundup = Math.ceil(vars.get(GRB.DoubleAttr.X)-0.01);
//	            		//vars.set(vars.get(GRB.DoubleAttr.LB), roundup);
//	            	}
					
					GRBVar[] yFracSol = new GRBVar[n*n*d];
					GRBVar[] xFracSol = new GRBVar[n*m1*d];
					int dem=0;
					int[][] w= new int[n][n];
					int[] b_d= new int[d];
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							w[j1][j2]=g.getEdgeWeight(j1+1, j2+1);
								for (int i=0;i<demandArray.size();i++)
								{
									
									yFracSol[dem]= y1[i][j1][j2];
									dem++;
								}
							
						}
					dem=0;
					GRBVar rFracSol = r_l;
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								xFracSol[dem]= x1[i][k][j];
								dem++;
							}
					dem=0;
					for (int i=0;i<demandArray.size();i++)
					{
						
						b_d[dem]= demandArray.get(i).bwS();
						dem++;
					}
					
					
					//Callback cb   = new Callback(yFracSol,d,n,w,b_d);
					Callback_cover cb   = new Callback_cover(rFracSol,xFracSol,yFracSol,d,n,m1,w,b_d,2,tau);
					
					model.setCallback(cb); 
					s0Size = cb.getS0();

//					
					//model.getEnv().set(GRB.IntParam.PreCrush,1);
					//model.setCallback(null); 
					//model.getEnv().set(GRB.DoubleParam.NodeLimit, GRB.INFINITY);
					//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
					//model.getEnv().set(GRB.IntParam.Cuts, 0);	
					model.update();
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
//						for(int i = 0; i < demandArray.size(); i++)
//							if(z1[i].get(GRB.DoubleAttr.X)>0)
//			    			{
//								//a_min++;
//			    			out.write(z1[i].get(GRB.StringAttr.VarName)
//			    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//			    			out.newLine();
//			    			}
////						out.write(r.get(GRB.StringAttr.VarName)
////		    					+ " : " +r.get(GRB.DoubleAttr.X));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
//									for(int i = 0; i < demandArray.size(); i++)
//										if(z1[i].get(GRB.DoubleAttr.X)>0)
//						    			{
//											//a_min++;
//						    			out.write(z1[i].get(GRB.StringAttr.VarName)
//						    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//						    			out.newLine();
//						    			}
////									out.write(r.get(GRB.StringAttr.VarName)
////					    					+ " : " +r.get(GRB.DoubleAttr.X));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
//							for(int i = 0; i < demandArray.size(); i++)
//								if(z1[i].get(GRB.DoubleAttr.X)>0)
//				    			{
//									//a_min++;
//				    			out.write(z1[i].get(GRB.StringAttr.VarName)
//				    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//				    			out.newLine();
//				    			}
////							out.write(r.get(GRB.StringAttr.VarName)
////			    					+ " : " +r.get(GRB.DoubleAttr.X));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
//					for(int i = 0; i < demandArray.size(); i++)
//						if(z1[i].get(GRB.DoubleAttr.X)>0)
//		    			{
//							//a_min++;
//		    			out.write(z1[i].get(GRB.StringAttr.VarName)
//		    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//		    			out.newLine();
//		    			}
////					out.write(r.get(GRB.StringAttr.VarName)
////	    					+ " : " +r.get(GRB.DoubleAttr.X));
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	}
	
	public static void Model_congestion(String outFile)
	{
		
		for(int i=0;i<demandArray.size();i++)
			demandArray.get(i).setMinbw(80);

		m_y= new GRBVar[demandArray.size()];
		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.000000001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,40);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			if(g.getEdgeWeight(j+1, k+1)>0)
				    			{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(demandArray.get(i).getMinbw(), demandArray.get(i).bwS(), demandArray.get(i).getMinbw(), GRB.INTEGER, st);
				    			}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								if(j1!=j2)
								{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								}
							}
				for (int i=0;i<demandArray.size();i++)
				{
					String st = "max_y["+(i+1)+ "]";
    				m_y[i] = model.addVar(demandArray.get(i).getMinbw(), demandArray.get(i).bwS(), demandArray.get(i).getMinbw(), GRB.INTEGER, st);
				}		
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				obj.addTerm(-1, r_l);
				for (int i=0;i<demandArray.size();i++)
				{
					obj.addTerm(1, m_y[i]);
				}	

				model.setObjective(obj,GRB.MAXIMIZE);	
					
				
				for(int i = 0; i < demandArray.size(); i++) 
				{
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    		GRBLinExpr expr2= new GRBLinExpr();
				    		if(g.getEdgeWeight(j+1, k+1)>0)
				    		{
				    		expr2.addTerm(1,y1[i][j][k]);
				    		}
							expr2.addTerm(-1,m_y[i]);
							String st = "aaa["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
				    		}
				}
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, g.getCap(j+1) , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(1,y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						int id = getDemand(i+1).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							model.addConstr(expr3, GRB.EQUAL, 1, st);
						}
						else
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						
						
						expr3 = null;
					}
				
//				for (int i =0;i<d;i++) //demand
//					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
//					{
//						GRBLinExpr expr3 = new GRBLinExpr();
//						for (int j=0;j<n;j++)// j is a node
//						{
//							expr3.addTerm(1, x1[i][k][j]);
//						}
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//								if(g.getEdgeWeight(j1+1, j2+1)>0)
//									expr3.addTerm(-1, y1[i][j1][j2]);
//						String st = "f1["+(i)+ "]["+(k)+ "]";
//						model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
//						expr3 = null;
//					}
				
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 2*demandArray.get(i).bwS(), st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								model.addConstr(expr7, GRB.LESS_EQUAL, demandArray.get(i).bwS(), st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								model.addConstr(expr7, GRB.GREATER_EQUAL, -demandArray.get(i).bwS(), st);
								expr7 = null;
							}
						}
					}
					
				}
				
				
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h2["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								model.addConstr(expr7, GRB.GREATER_EQUAL, demandArray.get(i).getMinbw(), st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								model.addConstr(expr7, GRB.LESS_EQUAL, -demandArray.get(i).getMinbw(), st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(demandArray.get(i).bwS(), phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
//				for (int j1=0;j1<n;j1++)
//					for(int j2=0;j2<n;j2++)
//					{
//						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
//						{
//							for(int i=0;i<demandArray.size();i++)
//								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(demandArray.get(i).getMinbw(), phi[i][k][j1][j2]);
//									exp.addTerm(-1,y1[i][j1][j2]);
//									String st = "i2["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//									
//								}
//						}
//					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
									model.addConstr(exp, GRB.EQUAL, -1, st);
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
//				for(int i = 0; i < demandArray.size(); i++) 
//					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
//						for(int j = 0; j < n; j++)
//						{
//							int source = demandArray.get(i).sourceS();
//							if(source != j+1)
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j1+1, j+1)>0)
//										exp.addTerm(-1, y1[i][j1][j]);
//								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j1+1, j+1)>0)
//										exp1.addTerm(1, y1[i][j1][j]);
//								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
//								exp1=null;
//							}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
//							
//						}
//			
			
				System.gc();
				
			
				
				// Optimize model
				try {
					
					model.optimize();
					model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						out.newLine();
						
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						
						out.write("Particularly,"+r_l);
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
//						for(int i = 0; i < demandArray.size(); i++)
//							if(z1[i].get(GRB.DoubleAttr.X)>0)
//			    			{
//								//a_min++;
//			    			out.write(z1[i].get(GRB.StringAttr.VarName)
//			    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//			    			out.newLine();
//			    			}
////						out.write(r.get(GRB.StringAttr.VarName)
////		    					+ " : " +r.get(GRB.DoubleAttr.X));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									out.write("Particularly,"+r_l+":"+r_n);
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
//									for(int i = 0; i < demandArray.size(); i++)
//										if(z1[i].get(GRB.DoubleAttr.X)>0)
//						    			{
//											//a_min++;
//						    			out.write(z1[i].get(GRB.StringAttr.VarName)
//						    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//						    			out.newLine();
//						    			}
////									out.write(r.get(GRB.StringAttr.VarName)
////					    					+ " : " +r.get(GRB.DoubleAttr.X));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						 out.write("Particularly,"+r_l+":"+r_n);
							out.newLine();
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
//							for(int i = 0; i < demandArray.size(); i++)
//								if(z1[i].get(GRB.DoubleAttr.X)>0)
//				    			{
//									//a_min++;
//				    			out.write(z1[i].get(GRB.StringAttr.VarName)
//				    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//				    			out.newLine();
//				    			}
////							out.write(r.get(GRB.StringAttr.VarName)
////			    					+ " : " +r.get(GRB.DoubleAttr.X));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					out.newLine();
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
//					for(int i = 0; i < demandArray.size(); i++)
//						if(z1[i].get(GRB.DoubleAttr.X)>0)
//		    			{
//							//a_min++;
//		    			out.write(z1[i].get(GRB.StringAttr.VarName)
//		    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//		    			out.newLine();
//		    			}
////					out.write(r.get(GRB.StringAttr.VarName)
////	    					+ " : " +r.get(GRB.DoubleAttr.X));
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	}
	public static void dynamic_heu5(ArrayList<Demand> DemandSet, MyGraph _gg)//su dung cho phan dynamic -> co the accept hoac reject
	{

		//PASO new

		x1= new GRBVar[DemandSet.size()][m1][n];//binary
		y1= new GRBVar[DemandSet.size()][n][n];//float (0,1)
		phi = new GRBVar[DemandSet.size()][m1+1][n][n];
		blocking = new GRBVar[DemandSet.size()];
		ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	ArrayList<Demand> dAcc= new ArrayList<>();
	       	
	       	

		double Const_No = 28.0;
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < DemandSet.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&_gg.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				
				for(int i=0;i<DemandSet.size();i++)
				{					
					obj.addTerm(-1, blocking[i]);
				}
				obj.addTerm(1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MINIMIZE);		
				//add constraints
				ex= new GRBLinExpr();
				ex.addTerm(1,r_l);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
				
				ex= new GRBLinExpr();
				ex.addTerm(1,r_n);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < DemandSet.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-_gg.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<DemandSet.size();i++) //demand
							{
								expr2.addTerm(DemandSet.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-_gg.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = DemandSet.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0&& _gg.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(_gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(_gg.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (_gg.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<DemandSet.size();i++)
								for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = DemandSet.get(i).sourceS();
							int destination = DemandSet.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = DemandSet.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = DemandSet.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(_gg.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(_gg.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(_gg.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
//						if(_gg.getEdgeWeight(desti, j1+1)>0)
//							expr13.addTerm(1, y1[i][desti-1][j1]);
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
			
				
				// Optimize model
				try {
					

					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'C');
					    		}
					
					
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					
					
					GRBVar[] yFracSol = new GRBVar[n*n*d];
					GRBVar[] xFracSol = new GRBVar[n*m1*d];
					int dem=0;
					int[][] w= new int[n][n];
					int[] b_d= new int[d];
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							w[j1][j2]=g.getEdgeWeight(j1+1, j2+1);
								for (int i=0;i<demandArray.size();i++)
								{
									
									yFracSol[dem]= y1[i][j1][j2];
									dem++;
								}
							
						}
					dem=0;
					GRBVar rFracSol = r_l;
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								xFracSol[dem]= x1[i][k][j];
								dem++;
							}
					dem=0;
					for (int i=0;i<demandArray.size();i++)
					{
						
						b_d[dem]= demandArray.get(i).bwS();
						dem++;
					}
					
					
					//Callback cb   = new Callback(yFracSol,d,n,w,b_d);
					Callback_cover cb   = new Callback_cover(rFracSol,xFracSol,yFracSol,d,n,m1,w,b_d,2,tau);
					
					model.setCallback(cb); 
					
					model.update();
					model.optimize();
					
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{

						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    		double _val = y1[i][j1][j2].get(GRB.DoubleAttr.X);
						    		y1[i][j1][j2].set(GRB.DoubleAttr.LB,_val );
						    		y1[i][j1][j2].set(GRB.DoubleAttr.UB, _val);
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{
						    			
						    			x1[i][k][j].set(GRB.CharAttr.VType, 'B');
						    		}
						
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
									{
										//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
											//if(j1!=j2)
										//{
						    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
										//}
									}
						System.out.println("Run optimization again....");
						model.update();
						
						model.optimize();
						//model.write("model1.lp");
						out.write("Solution for the problem:");
						out.newLine();
						optimstatus = model.get(GRB.IntAttr.Status); 
						if (optimstatus == GRB.Status.OPTIMAL) 
						{ 
							//r_min= r.get(GRB.DoubleAttr.X);
							value_final = obj.getValue();
//							out.write("Objective optimal Value: "+obj.getValue());
//							out.newLine();
							
							maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//							
//							out.write("Particularly,"+r_l+":"+r_n);
//							out.newLine();
												
							
							for(int i = 0; i < DemandSet.size(); i++) 
							{
								ArrayList<Integer> _loc = new ArrayList<>();
								for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
									_loc.add(-1);
								for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								{
									int id = DemandSet.get(i).getOrderFunction(k+1);
									for(int j = 0; j < n; j++)
							    		{	
							    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
							    			{
							    				if(id==-1)
							    				{
							    					System.out.println("Error");
							    					return;
							    				}
							    				else
							    				{
							    					_loc.set(id-1, j+1);
							    					break;
							    				}
							    			}
							    		}
								}
								if(_loc.get(0)!=-1)
								{
									//Demand nay duoc chap nhan
									funLoc.add(_loc);
									dAcc.add(DemandSet.get(i));
								}
							}
							
							for(int i = 0; i < DemandSet.size(); i++) 
							{
								System.out.println(DemandSet.get(i).toString());
								for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			}
							    		}
								if(dAcc.contains(DemandSet.get(i)))
								{

									ArrayList<Integer> _s = new ArrayList<>();
									int next = DemandSet.get(i).sourceS();
									while(true)//lap cho den khi next = destination
									{
										for(int j1=0;j1<n;j1++)
										{
											if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
											{
												_s.add(j1+1);
												next = j1+1;
												break;
											}
										}
										if(next==DemandSet.get(i).destinationS())
											break;
									}
									sol.add(_s);
								}
							}
							
							_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
					
						 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
						 	{ 
						        System.out.println("Model is infeasible or unbounded"); 
						        return;
						 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
						        	{ 
								        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
								        return; 
						        	} else if (optimstatus == GRB.Status.INTERRUPTED)
						        	{
						        		//r_min= r.get(GRB.DoubleAttr.X);
						        		value_final = obj.getValue();
//						        		out.write("Objective interrupt Value: "+obj.getValue());
//										out.newLine();
										maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
										maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//										out.write("Particularly,"+r_l+":"+r_n);
//										out.newLine();

										for(int i = 0; i < DemandSet.size(); i++) 
										{
											ArrayList<Integer> _loc = new ArrayList<>();
											for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
												_loc.add(-1);
											for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
											{
												int id = DemandSet.get(i).getOrderFunction(k+1);
												for(int j = 0; j < n; j++)
										    		{	
										    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
										    			{
										    				if(id==-1)
										    				{
										    					System.out.println("Error");
										    					return;
										    				}
										    				else
										    				{
										    					_loc.set(id-1, j+1);
										    					break;
										    				}
										    			}
										    		}
											}
											if(_loc.get(0)!=-1)
											{
												//Demand nay duoc chap nhan
												funLoc.add(_loc);
												dAcc.add(DemandSet.get(i));
											}
										}
										
										for(int i = 0; i < DemandSet.size(); i++) 
										{
											System.out.println(DemandSet.get(i).toString());
											for(int j1 = 0; j1 < n; j1++)
										    	for(int j2 = 0; j2 < n; j2++)
										    		{	
										    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
										    			{
										    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
										    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
										    			}
										    		}
											if(dAcc.contains(DemandSet.get(i)))
											{

												ArrayList<Integer> _s = new ArrayList<>();
												int next = DemandSet.get(i).sourceS();
												while(true)//lap cho den khi next = destination
												{
													for(int j1=0;j1<n;j1++)
													{
														if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
														{
															_s.add(j1+1);
															next = j1+1;
															break;
														}
													}
													if(next==DemandSet.get(i).destinationS())
														break;
												}
												sol.add(_s);
											}
										}
										
										_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
						        		
						        	}
						
						 else
						 {
							 //r_min= r.get(GRB.DoubleAttr.X);
							 value_final = obj.getValue();
//							 out.write("Objective feasible Value: "+obj.getValue());
//							 out.newLine();
							 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
								maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

								for(int i = 0; i < DemandSet.size(); i++) 
								{
									ArrayList<Integer> _loc = new ArrayList<>();
									for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
										_loc.add(-1);
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
									{
										int id = DemandSet.get(i).getOrderFunction(k+1);
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    				if(id==-1)
								    				{
								    					System.out.println("Error");
								    					return;
								    				}
								    				else
								    				{
								    					_loc.set(id-1, j+1);
								    					break;
								    				}
								    			}
								    		}
									}
									if(_loc.get(0)!=-1)
									{
										//Demand nay duoc chap nhan
										funLoc.add(_loc);
										dAcc.add(DemandSet.get(i));
									}
								}
								
								for(int i = 0; i < DemandSet.size(); i++) 
								{
									System.out.println(DemandSet.get(i).toString());
									for(int j1 = 0; j1 < n; j1++)
								    	for(int j2 = 0; j2 < n; j2++)
								    		{	
								    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
								    			{
								    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
								    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
								    			}
								    		}
									if(dAcc.contains(DemandSet.get(i)))
									{

										ArrayList<Integer> _s = new ArrayList<>();
										int next = DemandSet.get(i).sourceS();
										while(true)//lap cho den khi next = destination
										{
											for(int j1=0;j1<n;j1++)
											{
												if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
												{
													_s.add(j1+1);
													next = j1+1;
													break;
												}
											}
											if(next==DemandSet.get(i).destinationS())
												break;
										}
										sol.add(_s);
									}
								}
								
								_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
								
						  }
					
					}
					 
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
//					out.write("Objective interrupt Value: "+obj.getValue());
//					out.newLine();
//					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

					for(int i = 0; i < DemandSet.size(); i++) 
					{
						ArrayList<Integer> _loc = new ArrayList<>();
						for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
							_loc.add(-1);
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						{
							int id = DemandSet.get(i).getOrderFunction(k+1);
							for(int j = 0; j < n; j++)
					    		{	
					    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
					    			{
					    				if(id==-1)
					    				{
					    					System.out.println("Error");
					    					return;
					    				}
					    				else
					    				{
					    					_loc.set(id-1, j+1);
					    					break;
					    				}
					    			}
					    		}
						}
						if(_loc.get(0)!=-1)
						{
							//Demand nay duoc chap nhan
							funLoc.add(_loc);
							dAcc.add(DemandSet.get(i));
						}
					}
					
					for(int i = 0; i < DemandSet.size(); i++) 
					{
						System.out.println(DemandSet.get(i).toString());
						for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			}
					    		}
						if(dAcc.contains(DemandSet.get(i)))
						{

							ArrayList<Integer> _s = new ArrayList<>();
							int next = DemandSet.get(i).sourceS();
							while(true)//lap cho den khi next = destination
							{
								for(int j1=0;j1<n;j1++)
								{
									if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
									{
										_s.add(j1+1);
										next = j1+1;
										break;
									}
								}
								if(next==DemandSet.get(i).destinationS())
									break;
							}
							sol.add(_s);
						}
					}
					
					_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
	
	
	
	
	}
	public static void dynamic_heu4(ArrayList<Demand> DemandSet, MyGraph _gg)//su dung cho phan dynamic -> co the accept hoac reject
	{
		//PASO 

		x1= new GRBVar[DemandSet.size()][m1][n];//binary
		y1= new GRBVar[DemandSet.size()][n][n];//float (0,1)
		phi = new GRBVar[DemandSet.size()][m1+1][n][n];
		blocking = new GRBVar[DemandSet.size()];
		ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	ArrayList<Demand> dAcc= new ArrayList<>();
	       	
	       	

		double Const_No = 28.0;
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < DemandSet.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&_gg.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				
				for(int i=0;i<DemandSet.size();i++)
				{					
					obj.addTerm(-1, blocking[i]);
				}
				obj.addTerm(1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MINIMIZE);		
				//add constraints
				ex= new GRBLinExpr();
				ex.addTerm(1,r_l);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
				
				ex= new GRBLinExpr();
				ex.addTerm(1,r_n);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < DemandSet.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-_gg.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<DemandSet.size();i++) //demand
							{
								expr2.addTerm(DemandSet.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-_gg.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = DemandSet.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0&& _gg.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(_gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(_gg.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (_gg.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<DemandSet.size();i++)
								for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = DemandSet.get(i).sourceS();
							int destination = DemandSet.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = DemandSet.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = DemandSet.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(_gg.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(_gg.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(_gg.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
//						if(_gg.getEdgeWeight(desti, j1+1)>0)
//							expr13.addTerm(1, y1[i][desti-1][j1]);
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
			
				
				// Optimize model
				try {
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'C');
					    		}
					
					
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					
					
					model.update();
					model.optimize();
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{

						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    		double _val = y1[i][j1][j2].get(GRB.DoubleAttr.X);
						    		y1[i][j1][j2].set(GRB.DoubleAttr.LB,_val );
						    		y1[i][j1][j2].set(GRB.DoubleAttr.UB, _val);
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{
						    			
						    			x1[i][k][j].set(GRB.CharAttr.VType, 'B');
						    		}
						
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
									{
										//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
											//if(j1!=j2)
										//{
						    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
										//}
									}
						System.out.println("Run optimization again....");
						model.update();
						
						model.optimize();
						//model.write("model1.lp");
						out.write("Solution for the problem:");
						out.newLine();
						optimstatus = model.get(GRB.IntAttr.Status); 
						if (optimstatus == GRB.Status.OPTIMAL) 
						{ 
							//r_min= r.get(GRB.DoubleAttr.X);
							value_final = obj.getValue();
//							out.write("Objective optimal Value: "+obj.getValue());
//							out.newLine();
							
							maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//							
//							out.write("Particularly,"+r_l+":"+r_n);
//							out.newLine();
												
							
							for(int i = 0; i < DemandSet.size(); i++) 
							{
								ArrayList<Integer> _loc = new ArrayList<>();
								for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
									_loc.add(-1);
								for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								{
									int id = DemandSet.get(i).getOrderFunction(k+1);
									for(int j = 0; j < n; j++)
							    		{	
							    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
							    			{
							    				if(id==-1)
							    				{
							    					System.out.println("Error");
							    					return;
							    				}
							    				else
							    				{
							    					_loc.set(id-1, j+1);
							    					break;
							    				}
							    			}
							    		}
								}
								if(_loc.get(0)!=-1)
								{
									//Demand nay duoc chap nhan
									funLoc.add(_loc);
									dAcc.add(DemandSet.get(i));
								}
							}
							
							for(int i = 0; i < DemandSet.size(); i++) 
							{
								System.out.println(DemandSet.get(i).toString());
								for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			}
							    		}
								if(dAcc.contains(DemandSet.get(i)))
								{

									ArrayList<Integer> _s = new ArrayList<>();
									int next = DemandSet.get(i).sourceS();
									while(true)//lap cho den khi next = destination
									{
										for(int j1=0;j1<n;j1++)
										{
											if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
											{
												_s.add(j1+1);
												next = j1+1;
												break;
											}
										}
										if(next==DemandSet.get(i).destinationS())
											break;
									}
									sol.add(_s);
								}
							}
							
							_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
					
						 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
						 	{ 
						        System.out.println("Model is infeasible or unbounded"); 
						        return;
						 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
						        	{ 
								        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
								        return; 
						        	} else if (optimstatus == GRB.Status.INTERRUPTED)
						        	{
						        		//r_min= r.get(GRB.DoubleAttr.X);
						        		value_final = obj.getValue();
//						        		out.write("Objective interrupt Value: "+obj.getValue());
//										out.newLine();
										maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
										maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//										out.write("Particularly,"+r_l+":"+r_n);
//										out.newLine();

										for(int i = 0; i < DemandSet.size(); i++) 
										{
											ArrayList<Integer> _loc = new ArrayList<>();
											for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
												_loc.add(-1);
											for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
											{
												int id = DemandSet.get(i).getOrderFunction(k+1);
												for(int j = 0; j < n; j++)
										    		{	
										    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
										    			{
										    				if(id==-1)
										    				{
										    					System.out.println("Error");
										    					return;
										    				}
										    				else
										    				{
										    					_loc.set(id-1, j+1);
										    					break;
										    				}
										    			}
										    		}
											}
											if(_loc.get(0)!=-1)
											{
												//Demand nay duoc chap nhan
												funLoc.add(_loc);
												dAcc.add(DemandSet.get(i));
											}
										}
										
										for(int i = 0; i < DemandSet.size(); i++) 
										{
											System.out.println(DemandSet.get(i).toString());
											for(int j1 = 0; j1 < n; j1++)
										    	for(int j2 = 0; j2 < n; j2++)
										    		{	
										    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
										    			{
										    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
										    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
										    			}
										    		}
											if(dAcc.contains(DemandSet.get(i)))
											{

												ArrayList<Integer> _s = new ArrayList<>();
												int next = DemandSet.get(i).sourceS();
												while(true)//lap cho den khi next = destination
												{
													for(int j1=0;j1<n;j1++)
													{
														if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
														{
															_s.add(j1+1);
															next = j1+1;
															break;
														}
													}
													if(next==DemandSet.get(i).destinationS())
														break;
												}
												sol.add(_s);
											}
										}
										
										_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
						        		
						        	}
						
						 else
						 {
							 //r_min= r.get(GRB.DoubleAttr.X);
							 value_final = obj.getValue();
//							 out.write("Objective feasible Value: "+obj.getValue());
//							 out.newLine();
							 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
								maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

								for(int i = 0; i < DemandSet.size(); i++) 
								{
									ArrayList<Integer> _loc = new ArrayList<>();
									for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
										_loc.add(-1);
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
									{
										int id = DemandSet.get(i).getOrderFunction(k+1);
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    				if(id==-1)
								    				{
								    					System.out.println("Error");
								    					return;
								    				}
								    				else
								    				{
								    					_loc.set(id-1, j+1);
								    					break;
								    				}
								    			}
								    		}
									}
									if(_loc.get(0)!=-1)
									{
										//Demand nay duoc chap nhan
										funLoc.add(_loc);
										dAcc.add(DemandSet.get(i));
									}
								}
								
								for(int i = 0; i < DemandSet.size(); i++) 
								{
									System.out.println(DemandSet.get(i).toString());
									for(int j1 = 0; j1 < n; j1++)
								    	for(int j2 = 0; j2 < n; j2++)
								    		{	
								    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
								    			{
								    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
								    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
								    			}
								    		}
									if(dAcc.contains(DemandSet.get(i)))
									{

										ArrayList<Integer> _s = new ArrayList<>();
										int next = DemandSet.get(i).sourceS();
										while(true)//lap cho den khi next = destination
										{
											for(int j1=0;j1<n;j1++)
											{
												if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
												{
													_s.add(j1+1);
													next = j1+1;
													break;
												}
											}
											if(next==DemandSet.get(i).destinationS())
												break;
										}
										sol.add(_s);
									}
								}
								
								_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
								
						  }
					
					}
					 
					
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
//					out.write("Objective interrupt Value: "+obj.getValue());
//					out.newLine();
//					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

					for(int i = 0; i < DemandSet.size(); i++) 
					{
						ArrayList<Integer> _loc = new ArrayList<>();
						for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
							_loc.add(-1);
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						{
							int id = DemandSet.get(i).getOrderFunction(k+1);
							for(int j = 0; j < n; j++)
					    		{	
					    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
					    			{
					    				if(id==-1)
					    				{
					    					System.out.println("Error");
					    					return;
					    				}
					    				else
					    				{
					    					_loc.set(id-1, j+1);
					    					break;
					    				}
					    			}
					    		}
						}
						if(_loc.get(0)!=-1)
						{
							//Demand nay duoc chap nhan
							funLoc.add(_loc);
							dAcc.add(DemandSet.get(i));
						}
					}
					
					for(int i = 0; i < DemandSet.size(); i++) 
					{
						System.out.println(DemandSet.get(i).toString());
						for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			}
					    		}
						if(dAcc.contains(DemandSet.get(i)))
						{

							ArrayList<Integer> _s = new ArrayList<>();
							int next = DemandSet.get(i).sourceS();
							while(true)//lap cho den khi next = destination
							{
								for(int j1=0;j1<n;j1++)
								{
									if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
									{
										_s.add(j1+1);
										next = j1+1;
										break;
									}
								}
								if(next==DemandSet.get(i).destinationS())
									break;
							}
							sol.add(_s);
						}
					}
					
					_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
	
	
	
	}
	public static void dynamic_heu3(ArrayList<Demand> DemandSet, MyGraph _gg)//su dung cho phan dynamic -> co the accept hoac reject
	{
		//NOSO

		x1= new GRBVar[DemandSet.size()][m1][n];//binary
		y1= new GRBVar[DemandSet.size()][n][n];//float (0,1)
		phi = new GRBVar[DemandSet.size()][m1+1][n][n];
		blocking = new GRBVar[DemandSet.size()];
		ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	ArrayList<Demand> dAcc= new ArrayList<>();
	       	
	       	

		double Const_No = 28.0;
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < m1; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < DemandSet.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&_gg.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				
				for(int i=0;i<DemandSet.size();i++)
				{					
					obj.addTerm(-1, blocking[i]);
				}
				obj.addTerm(1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MINIMIZE);		
				//add constraints
				ex= new GRBLinExpr();
				ex.addTerm(1,r_l);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
				
				ex= new GRBLinExpr();
				ex.addTerm(1,r_n);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < DemandSet.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-_gg.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<DemandSet.size();i++) //demand
							{
								expr2.addTerm(DemandSet.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-_gg.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = DemandSet.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0&& _gg.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(_gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(_gg.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (_gg.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<DemandSet.size();i++)
								for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = DemandSet.get(i).sourceS();
							int destination = DemandSet.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = DemandSet.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = DemandSet.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(_gg.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(_gg.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(_gg.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
//						if(_gg.getEdgeWeight(desti, j1+1)>0)
//							expr13.addTerm(1, y1[i][desti-1][j1]);
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
			
				
				// Optimize model
				try {
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'C');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					
					
					model.update();
					model.optimize();
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
								{
									double _val = x1[i][k][j].get(GRB.DoubleAttr.X);
									x1[i][k][j].set(GRB.DoubleAttr.LB,_val );
									x1[i][k][j].set(GRB.DoubleAttr.UB, _val);
								}
							
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
							    			//{
							    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'B');
							    			//}
							    		}
							
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
										{
											//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
												//if(j1!=j2)
											//{
							    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
											//}
										}
							System.out.println("Run optimization again....");
							model.update();
							
							model.optimize();
							//model.write("model1.lp");
							out.write("Solution for the problem:");
							out.newLine();
						
							optimstatus = model.get(GRB.IntAttr.Status);

							if (optimstatus == GRB.Status.OPTIMAL) 
							{ 
								//r_min= r.get(GRB.DoubleAttr.X);
								value_final = obj.getValue();
//								out.write("Objective optimal Value: "+obj.getValue());
//								out.newLine();
								
								maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
								maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//								
//								out.write("Particularly,"+r_l+":"+r_n);
//								out.newLine();
													
								
								for(int i = 0; i < DemandSet.size(); i++) 
								{
									ArrayList<Integer> _loc = new ArrayList<>();
									for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
										_loc.add(-1);
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
									{
										int id = DemandSet.get(i).getOrderFunction(k+1);
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    				if(id==-1)
								    				{
								    					System.out.println("Error");
								    					return;
								    				}
								    				else
								    				{
								    					_loc.set(id-1, j+1);
								    					break;
								    				}
								    			}
								    		}
									}
									if(_loc.get(0)!=-1)
									{
										//Demand nay duoc chap nhan
										funLoc.add(_loc);
										dAcc.add(DemandSet.get(i));
									}
								}
								
								for(int i = 0; i < DemandSet.size(); i++) 
								{
									System.out.println(DemandSet.get(i).toString());
									for(int j1 = 0; j1 < n; j1++)
								    	for(int j2 = 0; j2 < n; j2++)
								    		{	
								    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
								    			{
								    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
								    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
								    			}
								    		}
									if(dAcc.contains(DemandSet.get(i)))
									{

										ArrayList<Integer> _s = new ArrayList<>();
										int next = DemandSet.get(i).sourceS();
										while(true)//lap cho den khi next = destination
										{
											for(int j1=0;j1<n;j1++)
											{
												if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
												{
													_s.add(j1+1);
													next = j1+1;
													break;
												}
											}
											if(next==DemandSet.get(i).destinationS())
												break;
										}
										sol.add(_s);
									}
								}
								
								_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
						
							 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
							 	{ 
							        System.out.println("Model is infeasible or unbounded"); 
							        return;
							 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
							        	{ 
									        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
									        return; 
							        	} else if (optimstatus == GRB.Status.INTERRUPTED)
							        	{
							        		//r_min= r.get(GRB.DoubleAttr.X);
							        		value_final = obj.getValue();
//							        		out.write("Objective interrupt Value: "+obj.getValue());
//											out.newLine();
											maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
											maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//											out.write("Particularly,"+r_l+":"+r_n);
//											out.newLine();

											for(int i = 0; i < DemandSet.size(); i++) 
											{
												ArrayList<Integer> _loc = new ArrayList<>();
												for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
													_loc.add(-1);
												for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
												{
													int id = DemandSet.get(i).getOrderFunction(k+1);
													for(int j = 0; j < n; j++)
											    		{	
											    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
											    			{
											    				if(id==-1)
											    				{
											    					System.out.println("Error");
											    					return;
											    				}
											    				else
											    				{
											    					_loc.set(id-1, j+1);
											    					break;
											    				}
											    			}
											    		}
												}
												if(_loc.get(0)!=-1)
												{
													//Demand nay duoc chap nhan
													funLoc.add(_loc);
													dAcc.add(DemandSet.get(i));
												}
											}
											
											for(int i = 0; i < DemandSet.size(); i++) 
											{
												System.out.println(DemandSet.get(i).toString());
												for(int j1 = 0; j1 < n; j1++)
											    	for(int j2 = 0; j2 < n; j2++)
											    		{	
											    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
											    			{
											    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
											    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
											    			}
											    		}
												if(dAcc.contains(DemandSet.get(i)))
												{

													ArrayList<Integer> _s = new ArrayList<>();
													int next = DemandSet.get(i).sourceS();
													while(true)//lap cho den khi next = destination
													{
														for(int j1=0;j1<n;j1++)
														{
															if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
															{
																_s.add(j1+1);
																next = j1+1;
																break;
															}
														}
														if(next==DemandSet.get(i).destinationS())
															break;
													}
													sol.add(_s);
												}
											}
											
											_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
							        		
							        	}
							
							 else
							 {
								 //r_min= r.get(GRB.DoubleAttr.X);
								 value_final = obj.getValue();
//								 out.write("Objective feasible Value: "+obj.getValue());
//								 out.newLine();
								 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

									for(int i = 0; i < DemandSet.size(); i++) 
									{
										ArrayList<Integer> _loc = new ArrayList<>();
										for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
											_loc.add(-1);
										for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										{
											int id = DemandSet.get(i).getOrderFunction(k+1);
											for(int j = 0; j < n; j++)
									    		{	
									    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
									    			{
									    				if(id==-1)
									    				{
									    					System.out.println("Error");
									    					return;
									    				}
									    				else
									    				{
									    					_loc.set(id-1, j+1);
									    					break;
									    				}
									    			}
									    		}
										}
										if(_loc.get(0)!=-1)
										{
											//Demand nay duoc chap nhan
											funLoc.add(_loc);
											dAcc.add(DemandSet.get(i));
										}
									}
									
									for(int i = 0; i < DemandSet.size(); i++) 
									{
										System.out.println(DemandSet.get(i).toString());
										for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			}
									    		}
										if(dAcc.contains(DemandSet.get(i)))
										{

											ArrayList<Integer> _s = new ArrayList<>();
											int next = DemandSet.get(i).sourceS();
											while(true)//lap cho den khi next = destination
											{
												for(int j1=0;j1<n;j1++)
												{
													if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
													{
														_s.add(j1+1);
														next = j1+1;
														break;
													}
												}
												if(next==DemandSet.get(i).destinationS())
													break;
											}
											sol.add(_s);
										}
									}
									
									_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
									
							  }
					}
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
//					out.write("Objective interrupt Value: "+obj.getValue());
//					out.newLine();
//					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

					for(int i = 0; i < DemandSet.size(); i++) 
					{
						ArrayList<Integer> _loc = new ArrayList<>();
						for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
							_loc.add(-1);
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						{
							int id = DemandSet.get(i).getOrderFunction(k+1);
							for(int j = 0; j < n; j++)
					    		{	
					    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
					    			{
					    				if(id==-1)
					    				{
					    					System.out.println("Error");
					    					return;
					    				}
					    				else
					    				{
					    					_loc.set(id-1, j+1);
					    					break;
					    				}
					    			}
					    		}
						}
						if(_loc.get(0)!=-1)
						{
							//Demand nay duoc chap nhan
							funLoc.add(_loc);
							dAcc.add(DemandSet.get(i));
						}
					}
					
					for(int i = 0; i < DemandSet.size(); i++) 
					{
						System.out.println(DemandSet.get(i).toString());
						for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			}
					    		}
						if(dAcc.contains(DemandSet.get(i)))
						{

							ArrayList<Integer> _s = new ArrayList<>();
							int next = DemandSet.get(i).sourceS();
							while(true)//lap cho den khi next = destination
							{
								for(int j1=0;j1<n;j1++)
								{
									if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
									{
										_s.add(j1+1);
										next = j1+1;
										break;
									}
								}
								if(next==DemandSet.get(i).destinationS())
									break;
							}
							sol.add(_s);
						}
					}
					
					_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
	
	
	}
	public static void dynamic_model(ArrayList<Demand> DemandSet, MyGraph _gg)//su dung cho phan dynamic -> co the accept hoac reject
	{
		x1= new GRBVar[DemandSet.size()][m1][n];//binary
		y1= new GRBVar[DemandSet.size()][n][n];//float (0,1)
		phi = new GRBVar[DemandSet.size()][m1+1][n][n];
		blocking = new GRBVar[DemandSet.size()];
		ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
		//thuc hien o day
	       
	       	ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
	       	ArrayList<Demand> dAcc= new ArrayList<>();
	       	
	       	

		double Const_No = 28.0;
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.001);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < DemandSet.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			if((j!=k)&&_gg.getEdgeWeight(j+1, k+1)>0)
				    			{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			}
				    		}
				
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				
				for(int i=0;i<DemandSet.size();i++)
				{					
					obj.addTerm(-1, blocking[i]);
				}
				obj.addTerm(1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MINIMIZE);		
				//add constraints
				ex= new GRBLinExpr();
				ex.addTerm(1,r_l);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
				
				ex= new GRBLinExpr();
				ex.addTerm(1,r_n);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < DemandSet.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-_gg.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<DemandSet.size();i++) //demand
							{
								expr2.addTerm(DemandSet.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-_gg.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = DemandSet.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<DemandSet.size();i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0&& _gg.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(_gg.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(_gg.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (_gg.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<DemandSet.size();i++)
								for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				for (int i=0;i<DemandSet.size();i++)
					for(int k=0;k<DemandSet.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = DemandSet.get(i).sourceS();
							int destination = DemandSet.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && _gg.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = DemandSet.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = DemandSet.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < DemandSet.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = DemandSet.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(_gg.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<DemandSet.size();i++)
				{
					int desti = DemandSet.get(i).destinationS();
					int source = DemandSet.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(_gg.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(_gg.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(_gg.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
//						if(_gg.getEdgeWeight(desti, j1+1)>0)
//							expr13.addTerm(1, y1[i][desti-1][j1]);
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
			
				
				// Optimize model
				try {
					
					model.optimize();
					model.write("model1.lp");
//					out.write("Solution for the problem:");
//					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
//						out.write("Objective optimal Value: "+obj.getValue());
//						out.newLine();
						
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//						
//						out.write("Particularly,"+r_l+":"+r_n);
//						out.newLine();
											
						
						for(int i = 0; i < DemandSet.size(); i++) 
						{
							ArrayList<Integer> _loc = new ArrayList<>();
							for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
								_loc.add(-1);
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							{
								int id = DemandSet.get(i).getOrderFunction(k+1);
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    				if(id==-1)
						    				{
						    					System.out.println("Error");
						    					return;
						    				}
						    				else
						    				{
						    					_loc.set(id-1, j+1);
						    					break;
						    				}
						    			}
						    		}
							}
							if(_loc.get(0)!=-1)
							{
								//Demand nay duoc chap nhan
								funLoc.add(_loc);
								dAcc.add(DemandSet.get(i));
							}
						}
						
						for(int i = 0; i < DemandSet.size(); i++) 
						{
							System.out.println(DemandSet.get(i).toString());
							for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			}
						    		}
							if(dAcc.contains(DemandSet.get(i)))
							{

								ArrayList<Integer> _s = new ArrayList<>();
								int next = DemandSet.get(i).sourceS();
								while(true)//lap cho den khi next = destination
								{
									for(int j1=0;j1<n;j1++)
									{
										if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
										{
											_s.add(j1+1);
											next = j1+1;
											break;
										}
									}
									if(next==DemandSet.get(i).destinationS())
										break;
								}
								sol.add(_s);
							}
						}
						
						_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
//					        		out.write("Objective interrupt Value: "+obj.getValue());
//									out.newLine();
									maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
//									out.write("Particularly,"+r_l+":"+r_n);
//									out.newLine();

									for(int i = 0; i < DemandSet.size(); i++) 
									{
										ArrayList<Integer> _loc = new ArrayList<>();
										for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
											_loc.add(-1);
										for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										{
											int id = DemandSet.get(i).getOrderFunction(k+1);
											for(int j = 0; j < n; j++)
									    		{	
									    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
									    			{
									    				if(id==-1)
									    				{
									    					System.out.println("Error");
									    					return;
									    				}
									    				else
									    				{
									    					_loc.set(id-1, j+1);
									    					break;
									    				}
									    			}
									    		}
										}
										if(_loc.get(0)!=-1)
										{
											//Demand nay duoc chap nhan
											funLoc.add(_loc);
											dAcc.add(DemandSet.get(i));
										}
									}
									
									for(int i = 0; i < DemandSet.size(); i++) 
									{
										System.out.println(DemandSet.get(i).toString());
										for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			}
									    		}
										if(dAcc.contains(DemandSet.get(i)))
										{

											ArrayList<Integer> _s = new ArrayList<>();
											int next = DemandSet.get(i).sourceS();
											while(true)//lap cho den khi next = destination
											{
												for(int j1=0;j1<n;j1++)
												{
													if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
													{
														_s.add(j1+1);
														next = j1+1;
														break;
													}
												}
												if(next==DemandSet.get(i).destinationS())
													break;
											}
											sol.add(_s);
										}
									}
									
									_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
//						 out.write("Objective feasible Value: "+obj.getValue());
//						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

							for(int i = 0; i < DemandSet.size(); i++) 
							{
								ArrayList<Integer> _loc = new ArrayList<>();
								for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
									_loc.add(-1);
								for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								{
									int id = DemandSet.get(i).getOrderFunction(k+1);
									for(int j = 0; j < n; j++)
							    		{	
							    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
							    			{
							    				if(id==-1)
							    				{
							    					System.out.println("Error");
							    					return;
							    				}
							    				else
							    				{
							    					_loc.set(id-1, j+1);
							    					break;
							    				}
							    			}
							    		}
								}
								if(_loc.get(0)!=-1)
								{
									//Demand nay duoc chap nhan
									funLoc.add(_loc);
									dAcc.add(DemandSet.get(i));
								}
							}
							
							for(int i = 0; i < DemandSet.size(); i++) 
							{
								System.out.println(DemandSet.get(i).toString());
								for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			}
							    		}
								if(dAcc.contains(DemandSet.get(i)))
								{

									ArrayList<Integer> _s = new ArrayList<>();
									int next = DemandSet.get(i).sourceS();
									while(true)//lap cho den khi next = destination
									{
										for(int j1=0;j1<n;j1++)
										{
											if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
											{
												_s.add(j1+1);
												next = j1+1;
												break;
											}
										}
										if(next==DemandSet.get(i).destinationS())
											break;
									}
									sol.add(_s);
								}
							}
							
							_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
//					out.write("Objective interrupt Value: "+obj.getValue());
//					out.newLine();
//					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);

					for(int i = 0; i < DemandSet.size(); i++) 
					{
						ArrayList<Integer> _loc = new ArrayList<>();
						for(int fID =0;fID<DemandSet.get(i).getFunctions().length;fID++)
							_loc.add(-1);
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						{
							int id = DemandSet.get(i).getOrderFunction(k+1);
							for(int j = 0; j < n; j++)
					    		{	
					    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
					    			{
					    				if(id==-1)
					    				{
					    					System.out.println("Error");
					    					return;
					    				}
					    				else
					    				{
					    					_loc.set(id-1, j+1);
					    					break;
					    				}
					    			}
					    		}
						}
						if(_loc.get(0)!=-1)
						{
							//Demand nay duoc chap nhan
							funLoc.add(_loc);
							dAcc.add(DemandSet.get(i));
						}
					}
					
					for(int i = 0; i < DemandSet.size(); i++) 
					{
						System.out.println(DemandSet.get(i).toString());
						for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(_gg.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			}
					    		}
						if(dAcc.contains(DemandSet.get(i)))
						{

							ArrayList<Integer> _s = new ArrayList<>();
							int next = DemandSet.get(i).sourceS();
							while(true)//lap cho den khi next = destination
							{
								for(int j1=0;j1<n;j1++)
								{
									if(_gg.getEdgeWeight(next, j1+1)>0&&y1[i][next-1][j1].get(GRB.DoubleAttr.X)>0)
									{
										_s.add(j1+1);
										next = j1+1;
										break;
									}
								}
								if(next==DemandSet.get(i).destinationS())
									break;
							}
							sol.add(_s);
						}
					}
					
					_solSet = new solSet(dAcc, sol, funLoc, DemandSet.size()-dAcc.size());					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
	
	}
	
	public static void dynamic_model(String outFile)//su dung cho phan dynamic -> co the accept hoac reject
	{
		

		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,4);
				env.set(GRB.IntParam.Presolve,0);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.CONTINUOUS, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
//				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = demandArray.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
			
				
				// Optimize model
				try {
					
					model.optimize();
					model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						out.newLine();
						
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						finalRunTime = model.get(GRB.DoubleAttr.Runtime);
						out.write("Particularly,"+r_l+":"+r_n);
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
//						for(int i = 0; i < demandArray.size(); i++)
//							if(z1[i].get(GRB.DoubleAttr.X)>0)
//			    			{
//								//a_min++;
//			    			out.write(z1[i].get(GRB.StringAttr.VarName)
//			    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//			    			out.newLine();
//			    			}
////						out.write(r.get(GRB.StringAttr.VarName)
////		    					+ " : " +r.get(GRB.DoubleAttr.X));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
									_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									finalRunTime = model.get(GRB.DoubleAttr.Runtime);
									out.write("Particularly,"+r_l+":"+r_n);
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
//									for(int i = 0; i < demandArray.size(); i++)
//										if(z1[i].get(GRB.DoubleAttr.X)>0)
//						    			{
//											//a_min++;
//						    			out.write(z1[i].get(GRB.StringAttr.VarName)
//						    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//						    			out.newLine();
//						    			}
////									out.write(r.get(GRB.StringAttr.VarName)
////					    					+ " : " +r.get(GRB.DoubleAttr.X));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							finalRunTime = model.get(GRB.DoubleAttr.Runtime);
						 out.write("Particularly,"+r_l+":"+r_n);
							out.newLine();
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
//							for(int i = 0; i < demandArray.size(); i++)
//								if(z1[i].get(GRB.DoubleAttr.X)>0)
//				    			{
//									//a_min++;
//				    			out.write(z1[i].get(GRB.StringAttr.VarName)
//				    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//				    			out.newLine();
//				    			}
////							out.write(r.get(GRB.StringAttr.VarName)
////			    					+ " : " +r.get(GRB.DoubleAttr.X));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					finalRunTime = model.get(GRB.DoubleAttr.Runtime);
					out.newLine();
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
//					for(int i = 0; i < demandArray.size(); i++)
//						if(z1[i].get(GRB.DoubleAttr.X)>0)
//		    			{
//							//a_min++;
//		    			out.write(z1[i].get(GRB.StringAttr.VarName)
//		    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//		    			out.newLine();
//		    			}
////					out.write(r.get(GRB.StringAttr.VarName)
////	    					+ " : " +r.get(GRB.DoubleAttr.X));
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	}
static public void combinations(int noComb, ArrayList<Integer> arr, ArrayList<Integer> list,int startPoisition,ArrayList<ArrayList<Integer>> result) {
		
		
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
	static public ArrayList<ArrayList<Integer>> FindCover(ArrayList<Integer> idSet, int[] b_d,int _w, int noCover)
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
	static protected int[] sortVal(ArrayList<Double> srcLst1)
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
	public static void Cover_Oct(String outFile)
	{



		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				//model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				model.getEnv().set(GRB.IntParam.Presolve,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
	//variable declaire
				
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = demandArray.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
				
			s0Size = 0;
				
				// Optimize model
				try {
					
					//int p = 100;
					//double alpha = 0.9;
					ArrayList<Integer> zeroSet = new ArrayList<>();
					ArrayList<Integer> oneSet = new ArrayList<>();
					//GRBVar[] vars = model.getVars();
					//int length = model.getVars().length;
					ArrayList<GRBVar> varsArr = new ArrayList<>();
					
					int dem=0;
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								dem++;
								varsArr.add( x1[i][k][j]);
								
							}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				varsArr.add(y1[i][j1][j2]);
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
											varsArr.add(phi[i][k][j1][j2]);
									//}
								}
					dem=0;
					GRBVar[] vars = new GRBVar[varsArr.size()];
					for(GRBVar v: varsArr)
						vars[dem++]= v;
						//set x1, y1, phi ro rang
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								x1[i][k][j].set(GRB.CharAttr.VType, 'C');
							}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'C');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					
					for(int i = 0; i < demandArray.size(); i++) 
					{
						blocking[i].set(GRB.CharAttr.VType, 'C');
					}
					int[] b_d = new int[demandArray.size()];
					for(int i=0;i<demandArray.size();i++)
						b_d[i]=demandArray.get(i).bwS();
					int noCoverCut =0;
					while(true)
					{
						int count = 0;
						model.update();
						model.optimize();
						
					
						
						//int optimstatus = model.get(GRB.IntAttr.Status); 
						//if (optimstatus == GRB.Status.OPTIMAL) 
						//{ 
							///TODO	
							
							
//							for(int i = 0; i < demandArray.size(); i++) 
//							    for(int j1 = 0; j1 < n; j1++)
//							    	for(int j2 = 0; j2 < n; j2++)
//							    		{	
//							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
//							    			{
//							    			System.out.println(y1[i][j1][j2].get(GRB.StringAttr.VarName)
//							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
//							    			//out.newLine();
//							    			}
//							    		}
							
							  for(int j1=0;j1<n;j1++)
						        	for(int j2=0;j2<n;j2++)
						        	{
			        		if(g.getEdgeWeight(j1+1,j2+1)>0)
			        		{
			        			
			        			ArrayList<Double> ySubTemp = new ArrayList<>();
			        			ArrayList<Integer> idYsubTemp = new ArrayList<>();

				        		//double[] ySubTemp = new double[d];
				        		for(int k=0;k<d;k++)
				        		{
				        				if(y1[k][j1][j2].get(GRB.DoubleAttr.X)-0.5 <0)
				        					ySubTemp.add(-y1[k][j1][j2].get(GRB.DoubleAttr.X)+0.5);
				        				else
				        					ySubTemp.add(y1[k][j1][j2].get(GRB.DoubleAttr.X)-0.5);
				        				idYsubTemp.add(k);
				        		}
				        		
				        		int[] ySorted= sortVal(ySubTemp);
				        		//int[] ySorted= sortDecreasing(ySubTemp);
				        		if (ySorted==null)
				        			continue;
				        		double sum=0;
				        		int index=-1;
				        		for(int id=0;id<ySorted.length;id++)
				        		{
				        			int idY=idYsubTemp.get(ySorted[id]);
				        			sum+=demandArray.get(idY).bwS();
				        			if(sum>g.getEdgeWeight(j1+1,j2+1))
				        			{
				        				index=id+1;
				        				break;
				        			}
				        				
				        		}
				        		ArrayList<Integer> coverSetTemp = new ArrayList<>();
				        		ArrayList<ArrayList<Integer>> coverSet = new ArrayList<>();
				        		if(index==-1)
				        		{
				        			System.out.println("khong lam gi");
				        			continue;
				        		}
				        		else
				        		{
				        			int temp = index+tau;
				        			if(tau==0)
				        				coverSet = FindCover(coverSetTemp, b_d, g.getEdgeWeight(j1+1, j2+1), index);
				        			else
				        			{
				        				while(temp!=index)
					        			{
					        				if (temp<=demandArray.size())
						        			{
						        				for (int i=0;i<temp;i++)
						        					coverSetTemp.add(idYsubTemp.get(ySorted[i]));
						        				coverSet = FindCover(coverSetTemp, b_d, g.getEdgeWeight(j1+1, j2+1), index);
						        				break;
						        			}
						        			else
						        			{
						        				System.out.println("vuot qua mang");
						        				temp--;
						        					
						        			}
					        			}
				        			}
				        			
				        			
				        		}
				        		if(coverSet.size()>0)
				        		{
				        			
				        			//System.out.println("So= " + coverSet.size());
				        			for (ArrayList<Integer> cover: coverSet)
				        			{
				        				
				        				sum =0.0;
				        				for(int i=0;i<cover.size();i++)
										{
											int idY=cover.get(i);
											sum+=b_d[idY];
										}
										double lambda = sum-g.getEdgeWeight(j1+1, j2+1);
										sum =0.0;
										for(int i=0;i<cover.size();i++)
										{
											int idDemand = cover.get(i);
											double bwD = b_d[idDemand];
											
											int id = idDemand + j2*d+j1*n*d;
											sum += bwD * y1[idDemand][j1][j2].get(GRB.DoubleAttr.X);					
											
											if(bwD>lambda)
											{
												sum += (bwD-lambda)*(1-y1[idDemand][j1][j2].get(GRB.DoubleAttr.X));
											}
										}
									
										double hs = 0;
										if(r_l.get(GRB.DoubleAttr.X)<0.3)
											hs = 3*r_l.get(GRB.DoubleAttr.X);
										else
										{
											if(r_l.get(GRB.DoubleAttr.X)<0.6)
												hs= 1.5*r_l.get(GRB.DoubleAttr.X);
											else
												hs=r_l.get(GRB.DoubleAttr.X);
										}
										hs=r_l.get(GRB.DoubleAttr.X);
										if(sum <= hs*g.getEdgeWeight(j1+1, j2+1))
										{
											//System.out.println("No violation");
											continue;
										}
										else
										{
											//System.out.println("Violated Inequality :" + rvalues);
										}
										if(s0Size < cover.size())
											s0Size = cover.size();
						        		GRBLinExpr exp = new GRBLinExpr();	
										//String st = "cover["+(j1)+ "]["+(j2)+ "]";
										sum =0.0;
										for(int i=0;i<cover.size();i++)
										{
											int idY=cover.get(i);
											sum+=b_d[idY];
										}
										lambda = sum-g.getEdgeWeight(j1+1, j2+1)*r_l.get(GRB.DoubleAttr.X);
										for(int i=0;i<cover.size();i++)
										{
											int idDemand = cover.get(i);
											double bwD = b_d[idDemand];
											
											int id = idDemand + j2*d+j1*n*d;
											exp.addTerm(bwD, y1[idDemand][j1][j2]);					
											
											if(bwD>lambda)
											{
												exp.addConstant(bwD-lambda);
												exp.addTerm(lambda-bwD,y1[idDemand][j1][j2]);
											}
										}
										//exp.addConstant(-w[j1][j2]+lambda);
										noCoverCut++;
										
										//System.out.println("khong vao a: "+ s0All +","+ s0Count);   
										String st = "Cover " + noCoverCut;
										exp.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
										model.addConstr(exp, GRB.LESS_EQUAL, 0,st);
										
										//addCut(exp, GRB.LESS_EQUAL, w[j1][j2]);
										
										exp=null; 
				        			}
				        		}
								
			        		}      		
			        		
			        	}

						//}
						if(noCoverCut>200)
							break;
					}
					noCoverFlow = noCoverCut;
		      
					System.out.println("chay optimal");	
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								x1[i][k][j].set(GRB.CharAttr.VType, 'B');
							}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'B');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
									//}
								}
					for(int i = 0; i < demandArray.size(); i++) 
					{
						blocking[i].set(GRB.CharAttr.VType, 'B');
					}
					model.update();
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					
					
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	
	}
	public static void Cover_new(String outFile)// 06/09/2017
	{


		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				model.getEnv().set(GRB.IntParam.Presolve,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = demandArray.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
			
				
				// Optimize model
				try {
					//model.getEnv().set(GRB.DoubleParam.NodeLimit, 1500);
//					GRBModel m_relax = model.relax();
//					m_relax.optimize();
//					GRBVar[] n_vars = m_relax.getVars();
//					for(GRBVar vars: n_vars)
//	            	{						
//	            		double roundup = Math.ceil(vars.get(GRB.DoubleAttr.X)-0.01);
//	            		//vars.set(vars.get(GRB.DoubleAttr.LB), roundup);
//	            	}
					
					
					GRBVar[] yFracSol = new GRBVar[n*n*d];
					GRBVar[] xFracSol = new GRBVar[n*m1*d];
					int dem=0;
					int[][] w= new int[n][n];
					int[] b_d= new int[d];
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							w[j1][j2]=g.getEdgeWeight(j1+1, j2+1);
								for (int i=0;i<demandArray.size();i++)
								{
									
									yFracSol[dem]= y1[i][j1][j2];
									dem++;
								}
							
						}
					dem=0;
					GRBVar rFracSol = r_l;
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								xFracSol[dem]= x1[i][k][j];
								dem++;
							}
					dem=0;
					for (int i=0;i<demandArray.size();i++)
					{
						
						b_d[dem]= demandArray.get(i).bwS();
						dem++;
					}
					
					
					//Callback cb   = new Callback(yFracSol,d,n,w,b_d);
					Callback_cover cb   = new Callback_cover(rFracSol,xFracSol,yFracSol,d,n,m1,w,b_d,2,tau);
					
					model.setCallback(cb); 
					
//					
					//model.getEnv().set(GRB.IntParam.PreCrush,1);
					//model.setCallback(null); 
					//model.getEnv().set(GRB.DoubleParam.NodeLimit, GRB.INFINITY);
					//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
					//model.getEnv().set(GRB.IntParam.Cuts, 0);	
					model.update();
					
					model.optimize();
					
					
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						s0Size = cb.getS0();
						noCoverFlow = cb.getnoCoverCut();
						System.out.println("Flow cover:::::" + s0Size +", no cover flow: "+ noCoverFlow );
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad = r_n.get(GRB.DoubleAttr.X);
						finalRunTime = model.get(GRB.DoubleAttr.Runtime);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						System.out.println(_gap + ":"+ _nodeBB);
						
						out.write("Objective optimal Value: "+obj.getValue());
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
//						for(int i = 0; i < demandArray.size(); i++)
//							if(z1[i].get(GRB.DoubleAttr.X)>0)
//			    			{
//								//a_min++;
//			    			out.write(z1[i].get(GRB.StringAttr.VarName)
//			    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//			    			out.newLine();
//			    			}
////						out.write(r.get(GRB.StringAttr.VarName)
////		    					+ " : " +r.get(GRB.DoubleAttr.X));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad = r_n.get(GRB.DoubleAttr.X);
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
									_gap = model.get(GRB.DoubleAttr.MIPGap);
									finalRunTime = model.get(GRB.DoubleAttr.Runtime);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									s0Size = cb.getS0();
									noCoverFlow = cb.getnoCoverCut();
									System.out.println("Flow cover:::::" + s0Size +", no cover flow: "+ noCoverFlow );
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
//									for(int i = 0; i < demandArray.size(); i++)
//										if(z1[i].get(GRB.DoubleAttr.X)>0)
//						    			{
//											//a_min++;
//						    			out.write(z1[i].get(GRB.StringAttr.VarName)
//						    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//						    			out.newLine();
//						    			}
////									out.write(r.get(GRB.StringAttr.VarName)
////					    					+ " : " +r.get(GRB.DoubleAttr.X));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad = r_n.get(GRB.DoubleAttr.X);
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							finalRunTime = model.get(GRB.DoubleAttr.Runtime);
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 s0Size = cb.getS0();
							noCoverFlow = cb.getnoCoverCut();
							System.out.println("Flow cover:::::" + s0Size +", no cover flow: "+ noCoverFlow );
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
//							for(int i = 0; i < demandArray.size(); i++)
//								if(z1[i].get(GRB.DoubleAttr.X)>0)
//				    			{
//									//a_min++;
//				    			out.write(z1[i].get(GRB.StringAttr.VarName)
//				    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//				    			out.newLine();
//				    			}
////							out.write(r.get(GRB.StringAttr.VarName)
////			    					+ " : " +r.get(GRB.DoubleAttr.X));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad = r_n.get(GRB.DoubleAttr.X);
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					finalRunTime = model.get(GRB.DoubleAttr.Runtime);
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
//					for(int i = 0; i < demandArray.size(); i++)
//						if(z1[i].get(GRB.DoubleAttr.X)>0)
//		    			{
//							//a_min++;
//		    			out.write(z1[i].get(GRB.StringAttr.VarName)
//		    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//		    			out.newLine();
//		    			}
////					out.write(r.get(GRB.StringAttr.VarName)
////	    					+ " : " +r.get(GRB.DoubleAttr.X));
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	}
	public static void Model_Minh(String outFile)
	{

		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.IntParam.Presolve ,0);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
				//variable declaire
				
			
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if(g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								if(j1!=j2)
								{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.CONTINUOUS, st);
								}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				model.update();

				//obj.addTerm(1, r_l);
				//obj.addTerm(1, r_n);
				obj.addTerm(1, r);

				model.setObjective(obj,GRB.MINIMIZE);		
				//add constraints
				GRBLinExpr ex= new GRBLinExpr();
				ex.addTerm(1,r_l);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
				
				ex= new GRBLinExpr();
				ex.addTerm(1,r_n);
				ex.addTerm(-1,r);
				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						int id = getDemand(i+1).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							model.addConstr(expr3, GRB.EQUAL, 1, st);
						}
						else
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								model.addConstr(expr7, GRB.EQUAL, 1, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								model.addConstr(expr7, GRB.EQUAL, -1, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
									model.addConstr(exp, GRB.EQUAL, -1, st);
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
//							}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
			
				System.gc();
				
			
				
				// Optimize model
				try {
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						out.newLine();
						
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
		        		value_final = obj.getValue();
		        		_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						out.write("Particularly,"+r_l+":"+r_n);
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
//						for(int i = 0; i < demandArray.size(); i++)
//							if(z1[i].get(GRB.DoubleAttr.X)>0)
//			    			{
//								//a_min++;
//			    			out.write(z1[i].get(GRB.StringAttr.VarName)
//			    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//			    			out.newLine();
//			    			}
////						out.write(r.get(GRB.StringAttr.VarName)
////		    					+ " : " +r.get(GRB.DoubleAttr.X));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
									out.write("Particularly,"+r_l+":"+r_n);
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
//									for(int i = 0; i < demandArray.size(); i++)
//										if(z1[i].get(GRB.DoubleAttr.X)>0)
//						    			{
//											//a_min++;
//						    			out.write(z1[i].get(GRB.StringAttr.VarName)
//						    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//						    			out.newLine();
//						    			}
////									out.write(r.get(GRB.StringAttr.VarName)
////					    					+ " : " +r.get(GRB.DoubleAttr.X));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
			        		value_final = obj.getValue();
			        		_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						 out.write("Particularly,"+r_l+":"+r_n);
							out.newLine();
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
//							for(int i = 0; i < demandArray.size(); i++)
//								if(z1[i].get(GRB.DoubleAttr.X)>0)
//				    			{
//									//a_min++;
//				    			out.write(z1[i].get(GRB.StringAttr.VarName)
//				    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//				    			out.newLine();
//				    			}
////							out.write(r.get(GRB.StringAttr.VarName)
////			    					+ " : " +r.get(GRB.DoubleAttr.X));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					out.write("Particularly,"+r_l+":"+r_n);
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
	        		value_final = obj.getValue();
	        		_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					out.newLine();
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
//					for(int i = 0; i < demandArray.size(); i++)
//						if(z1[i].get(GRB.DoubleAttr.X)>0)
//		    			{
//							//a_min++;
//		    			out.write(z1[i].get(GRB.StringAttr.VarName)
//		    					+ " : " +z1[i].get(GRB.DoubleAttr.X));
//		    			out.newLine();
//		    			}
////					out.write(r.get(GRB.StringAttr.VarName)
////	    					+ " : " +r.get(GRB.DoubleAttr.X));
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	}
	
	
	@SuppressWarnings("unchecked")
	public static void mainBasedHeu(String folderName, int p, double alpha)//based heuristic
	{

		//Cover
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				//int p = Integer.parseInt(args[1]);
				//double alpha = Double.parseDouble(args[2]);
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output1309/output_BasedHeu.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							ReadInputFile(file.getPath());
							//ReadInput(file.getPath());
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/BasedHeu_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							final long startTime = System.currentTimeMillis();
							basedHeuristic(str,p,alpha);
							_duration = System.currentTimeMillis() - startTime;
								out1.write(" "+m + " " +d +" "+n+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad + " "+_gap+" "+_nodeBB+" "+_acceptNo.intValue()+" "+ _duration);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	
	}
	public static void Heu3_1(String outFile)
	{




		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				//model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
	//variable declaire
				
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = demandArray.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
				
			
				
				// Optimize model
				try {
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'C');
					    		}
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'C');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					
					
					model.update();
					model.optimize();
					
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    		Double _val = y1[i][j1][j2].get(GRB.DoubleAttr.X);
					    		if(_val==0.0 || _val ==1.0)
					    		{
					    			y1[i][j1][j2].set(GRB.DoubleAttr.LB,_val.intValue() );
						    		y1[i][j1][j2].set(GRB.DoubleAttr.UB, _val.intValue());
					    		}
					    		
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
								Double _val = x1[i][k][j].get(GRB.DoubleAttr.X);
					    		if(_val==0.0 || _val ==1.0)
					    		{
					    			x1[i][k][j].set(GRB.DoubleAttr.LB,_val.intValue() );
					    			x1[i][k][j].set(GRB.DoubleAttr.UB, _val.intValue());
					    		}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									Double _val = phi[i][k][j1][j2].get(GRB.DoubleAttr.X);
						    		if(_val==0.0 || _val ==1.0)
						    		{
						    			phi[i][k][j1][j2].set(GRB.DoubleAttr.LB,_val.intValue() );
						    			phi[i][k][j1][j2].set(GRB.DoubleAttr.UB, _val.intValue());
						    		}
								}
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'B');
					    		}
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'B');
					    			//}
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
									//}
								}
					System.out.println("Run optimization again....");
					model.update();
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	
	
	}
	
	public static void Heu5(String outFile)//PASO + Flowcover
	{




		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,4000);
				GRBModel model = new GRBModel(env);
				//model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
	//variable declaire
				
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.BINARY, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r";
				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (5) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
									expr1.addTerm(getFunction(k+1).getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (6)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (8)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						
						int id = demandArray.get(i).getOrderFunction(k+1);
						String st = "f["+(i)+ "]["+(k)+ "]";
						if (id!=0)//truong hop function in demand =1
						{
							//expr3.addTerm(-1, z1[i]);
							expr3.addTerm(-1, blocking[i]);
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						else
						{
							
							model.addConstr(expr3, GRB.EQUAL, 0, st);
						}
						
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								exp.addTerm(1, x1[i][f1][j]);
								int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
				
			
				
				// Optimize model
				try {
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'C');
					    		}
					
					
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
									//}
								}
					
					
					GRBVar[] yFracSol = new GRBVar[n*n*d];
					GRBVar[] xFracSol = new GRBVar[n*m1*d];
					int dem=0;
					int[][] w= new int[n][n];
					int[] b_d= new int[d];
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							w[j1][j2]=g.getEdgeWeight(j1+1, j2+1);
								for (int i=0;i<demandArray.size();i++)
								{
									
									yFracSol[dem]= y1[i][j1][j2];
									dem++;
								}
							
						}
					dem=0;
					GRBVar rFracSol = r_l;
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
							{
								xFracSol[dem]= x1[i][k][j];
								dem++;
							}
					dem=0;
					for (int i=0;i<demandArray.size();i++)
					{
						
						b_d[dem]= demandArray.get(i).bwS();
						dem++;
					}
					
					
					//Callback cb   = new Callback(yFracSol,d,n,w,b_d);
					Callback_cover cb   = new Callback_cover(rFracSol,xFracSol,yFracSol,d,n,m1,w,b_d,2,tau);
					
					model.setCallback(cb); 
					
					model.update();
					model.optimize();
					
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    		double _val = y1[i][j1][j2].get(GRB.DoubleAttr.X);
					    		y1[i][j1][j2].set(GRB.DoubleAttr.LB,_val );
					    		y1[i][j1][j2].set(GRB.DoubleAttr.UB, _val);
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'B');
					    		}
					
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
										//if(j1!=j2)
									//{
					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
									//}
								}
					
					model.setCallback(null); 
					System.out.println("Run optimization again....");
					model.update();
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/2;
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
	    			out.newLine();
					
	
				}
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	
	
	}
	public static void Heu4(String outFile)//PASO
	{

		int SpineCount =0;

		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,70000);
				GRBModel model = new GRBModel(env);
				//model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
	//variable declaire
				
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.CONTINUOUS, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
//				st1 = "r";
//				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				//Constraint (11)
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				//Constraint (12)
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (4) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
								Function f_temp = demandArray.get(i).getFunctions()[k];
									expr1.addTerm(f_temp.getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (5)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (7)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						String st = "f["+(i)+ "]["+(k)+ "]";
						expr3.addTerm(-1, blocking[i]);
						model.addConstr(expr3, GRB.EQUAL, 0, st);
												
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								//int f2 = demandArray.get(i).getFunctions()[k].id()-1;
								int f2=k;
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								//int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								int f1= k-1;
								exp.addTerm(-1, x1[i][f1][j]);
								int f2 = k;
								//int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
				
			
				
				// Optimize model
				try {
					
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'C');
					    		}
					
					
					
//					for (int i=0;i<demandArray.size();i++)
//						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//							for(int j1=0;j1<n;j1++)
//								for(int j2=0;j2<n;j2++)
//								{
//									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//										//if(j1!=j2)
//									//{
//					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
//									//}
//								}
					
					
					model.update();
					model.optimize();
					
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    		double _val = y1[i][j1][j2].get(GRB.DoubleAttr.X);
					    		y1[i][j1][j2].set(GRB.DoubleAttr.LB,_val );
					    		y1[i][j1][j2].set(GRB.DoubleAttr.UB, _val);
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
						for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
							for(int j = 0; j < n; j++)
					    		{
					    			
					    			x1[i][k][j].set(GRB.CharAttr.VType, 'B');
					    		}
					
//					for (int i=0;i<demandArray.size();i++)
//						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//							for(int j1=0;j1<n;j1++)
//								for(int j2=0;j2<n;j2++)
//								{
//									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//										//if(j1!=j2)
//									//{
//					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
//									//}
//								}
					System.out.println("Run optimization again....");
					model.update();
					
					model.optimize();
					model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			if(g.getCap(j+1)>leafCapacity)
						    				SpineCount ++;
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			if(g.getCap(j+1)>leafCapacity)
								    				SpineCount ++;
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			if(g.getCap(j+1)>leafCapacity)
						    				SpineCount ++;
						    			}
						    			
						    				
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			if(g.getCap(j+1)>leafCapacity)
				    				SpineCount ++;
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
	    			out.newLine();
					
	
				}
				spineRatio = SpineCount*1.0/(m1*_acceptNo);
				System.out.println("Spine Ratio = "+ spineRatio);
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	
	}
	
	public static void newHeu (String outFile)//NOSO
	{

		int SpineCount=0;

		double Const_No = 28.0;
		try {

			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			out.write("number of function:" + m);
			out.newLine();
			for (int i=0;i<m;i++)
	       	{	 
	               out.write(functionArr[i].toString());
	               out.newLine();
	       	}
	   		out.write("number of Demand:" + d);
	   		out.newLine();
	       	for (int i=0;i<d;i++)
	       	{    		
	       		out.write(demandArray.get(i).toString());
	       		out.newLine();
	       	}
	       	out.write("virtual node:"+ n);
	       	out.newLine();
	       	for (int i=0;i<n;i++)
	       	{
	       		for (int j=0;j<n;j++)
	       			out.write(g.getEdgeWeight(i+1, j+1) + " ");
	       		out.newLine();
	       	}
	       	
	       	
	       	
			try{
				GRBEnv env = new GRBEnv("qp.log");
				env.set(GRB.DoubleParam.MIPGap, 0.0005);
				env.set(GRB.DoubleParam.FeasibilityTol, 0.000000001);
				env.set(GRB.IntParam.Threads,16);
				env.set(GRB.DoubleParam.TimeLimit,70000);
				GRBModel model = new GRBModel(env);
				//model.getEnv().set(GRB.IntParam.PreCrush,1);//add cut
				//model.getEnv().set(GRB.IntParam.FlowCoverCuts, 0);
				//model.getEnv().set(GRB.IntParam.Cuts, 0);
				//model.getEnv().set(GRB.DoubleParam.Heuristics,0);
				GRBLinExpr obj = new GRBLinExpr();
				int constant=1;
	
				
	//variable declaire
				
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{
				    			String st = "x1["+(i+1)+ "]["+(k+1)+ "]["+(j+1)+ "]";
				    			x1[i][k][j] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    		}
				for(int i = 0; i < demandArray.size(); i++) 
				    for(int j = 0; j < n; j++)
				    	for(int k = 0; k < n; k++)
				    		{
				    			//if((j!=k)&&g.getEdgeWeight(j+1, k+1)>0)
				    			//{
				    				String st = "y1["+(i+1)+ "]["+(j+1)+ "]["+(k+1)+ "]";
				    				y1[i][j][k] = model.addVar(0, 1, 0, GRB.BINARY, st);
				    			//}
				    		}
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								//{
									String st = "phi["+(i+1)+ "]["+(k+1)+ "]["+(j1+1)+ "]["+(j2+1)+ "]";
				    				phi[i][k][j1][j2] = model.addVar(0, 1, 0, GRB.CONTINUOUS, st);
								//}
							}
						
				
				String st1 = "r_l";
				r_l = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "r_n";
				r_n = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
//				st1 = "r";
//				r = model.addVar(0, 1, 0, GRB.CONTINUOUS, st1);
				st1 = "blocking";
				for(int i = 0; i < demandArray.size(); i++) 
				{
					st1="blocking["+i+"]";
					blocking[i]= model.addVar(0, 1, 0, GRB.BINARY, st1);
				}
				model.update();

				obj.addTerm(-1, r_l);
				obj.addTerm(-1, r_n);
				
				for(int i=0;i<demandArray.size();i++)
				{					
					obj.addTerm(10.0/demandArray.size(), blocking[i]);
				}
				//obj.addTerm(-1, r);
				GRBLinExpr ex= new GRBLinExpr();
				

				model.setObjective(obj,GRB.MAXIMIZE);		
				//add constraints
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_l);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[0]");
//				
//				ex= new GRBLinExpr();
//				ex.addTerm(1,r_n);
//				ex.addTerm(-1,r);
//				model.addConstr(ex, GRB.LESS_EQUAL, 0 , "r[1]");
					
				//neu demand bi block thi tat ca cac y deu bang 0
				
				//Constraint (11)
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(-1, blocking[i]);
								String st = "new["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
								expr3 = null;
							}
						}
				//Constraint (12)
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for(int j1=0;j1<n;j1++)
							for(int j2=0;j2<n;j2++)
							{
								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
								//if(j1!=j2)
								{
									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1, phi[i][k][j1][j2]);
									expr3.addTerm(-1, blocking[i]);
									String st = "newPhi["+(i)+ "]["+(k)+ "]["+(j1)+ "]["+(j2)+"]";
									model.addConstr(expr3, GRB.LESS_EQUAL, 0, st);
									expr3 = null;
								}
							}
					
//				
				//Eq (4) ->Ok
					for(int j = 0; j < n; j++) //node
			    	{
						GRBLinExpr expr1= new GRBLinExpr();
						for(int i = 0; i < demandArray.size(); i++) //demand
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++) //function
							{
								Function f_temp = demandArray.get(i).getFunctions()[k];
									expr1.addTerm(f_temp.getReq(),x1[i][k][j]);
							}
						expr1.addTerm(-g.getCap(j+1),r_n);
						String st = "c["+(j)+ "]";
						model.addConstr(expr1, GRB.LESS_EQUAL, 0 , st);
						expr1 = null;
			    	}
				System.gc();
				
				//Eq (5)->OK
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
						{
							GRBLinExpr expr2= new GRBLinExpr();
							for (int i =0;i<demandArray.size();i++) //demand
							{
								expr2.addTerm(demandArray.get(i).bwS(),y1[i][j1][j2]);
								//expr2.addTerm(demandArray.get(i).bwS(),y1[i][j2][j1]);
							}
							expr2.addTerm(-g.getEdgeWeight(j1+1, j2+1),r_l);
							String st = "d["+(j1+1)+ "]["+(j2+1)+ "]";
							model.addConstr(expr2, GRB.LESS_EQUAL,0, st);
							expr2 = null;	
						}
						
					}
				
			
				System.gc();
				
				//Eq (7)
				for (int i =0;i<d;i++) //demand
					for (int k = 0;k<demandArray.get(i).getFunctions().length;k++)//k is a function
					{
						GRBLinExpr expr3 = new GRBLinExpr();
						for (int j=0;j<n;j++)// j is a node
						{
							expr3.addTerm(1, x1[i][k][j]);
						}
						String st = "f["+(i)+ "]["+(k)+ "]";
						expr3.addTerm(-1, blocking[i]);
						model.addConstr(expr3, GRB.EQUAL, 0, st);
												
						expr3 = null;
					}
				//Eq 9
				for (int i =0;i<d;i++) //demand
					for (int j1=0;j1<n;j1++)
						for(int j2=0;j2<n;j2++)
						{
							if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0&& g.getEdgeWeight(j2+1, j1+1)>0)
							{
								GRBLinExpr expr3 = new GRBLinExpr();
								expr3.addTerm(1, y1[i][j1][j2]);
								expr3.addTerm(1, y1[i][j2][j1]);
								String st = "g["+(i)+ "]["+(j1)+ "]["+(j2)+"]";
								model.addConstr(expr3, GRB.LESS_EQUAL, 1, st);
								expr3 = null;
							}
							
						}
				System.gc();
				//Eq (10) ->ok
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					for (int j1=0;j1<n;j1++)
					{
						GRBLinExpr expr7= new GRBLinExpr();
						String st = "h1["+(i)+ "]["+(j1+1)+  "s]";
						for (int j2=0;j2<n;j2++)
						{
							if(g.getEdgeWeight(j1+1, j2+1)>0)
							{
								
								expr7.addTerm(1, y1[i][j1][j2]);
							}
							if(g.getEdgeWeight(j2+1, j1+1)>0)
								expr7.addTerm(-1, y1[i][j2][j1]);
								
						}
						
						if(j1 !=source-1 && j1 !=desti-1)
						{
							
							
							model.addConstr(expr7, GRB.EQUAL, 0, st);
							expr7 = null;
						}
						else
						{
							if(j1==source-1)
							{
								expr7.addTerm(-1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
							if(j1==desti-1)
							{
								expr7.addTerm(1, blocking[i]);
								model.addConstr(expr7, GRB.EQUAL, 0, st);
								expr7 = null;
							}
						}
					}
					
				}
				
				//Eq 11 new
				for (int j1=0;j1<n;j1++)
					for(int j2=0;j2<n;j2++)
					{
						if(j1!=j2 && (g.getEdgeWeight(j1+1, j2+1)>0))
						{
							for(int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								{
									GRBLinExpr exp = new GRBLinExpr();								
									exp.addTerm(1, phi[i][k][j1][j2]);
									exp.addTerm(-1,y1[i][j1][j2]);
									String st = "i1["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
									model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
									
								}
						}
					}
				
				//Eq 11b new
				
				for (int i=0;i<demandArray.size();i++)
					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
						for (int j=0;j<n;j++)
						{
							int source = demandArray.get(i).sourceS();
							int destination = demandArray.get(i).destinationS();
							GRBLinExpr exp = new GRBLinExpr();
							for (int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
								{
									if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
									{
										if(j==j1)
										{
											exp.addTerm(-1, phi[i][k][j1][j2]);
										}
										if(j==j2)
										{
											exp.addTerm(1, phi[i][k][j1][j2]);
										}
									}
								}
							if(k==0)
							{
								//int f2 = demandArray.get(i).getFunctions()[k].id()-1;
								int f2=k;
								exp.addTerm(-1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								if(j==source-1)
								{
									exp.addTerm(1, blocking[i]);
									model.addConstr(exp, GRB.EQUAL, 0, st);
								}
								else
									model.addConstr(exp, GRB.EQUAL, 0, st);
								
							}
							else
							{
								//int f1 = demandArray.get(i).getFunctions()[k-1].id()-1;
								int f1= k-1;
								exp.addTerm(-1, x1[i][f1][j]);
								int f2 = k;
								//int f2 = demandArray.get(i).getFunctions()[k].id()-1;							
								exp.addTerm(1, x1[i][f2][j]);
								String st = "i2["+(i)+ "]["+(k)+ "]["+(j+1)+ "]";
								model.addConstr(exp, GRB.EQUAL, 0, st);
								
								
							}
							
						}
				
				//Eq 11 new
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int j=0;j<n;j++)
//					{
//						for (int k=0;k<demandArray.get(i).getFunctions().length-1;k++)
//						{
//							int f1 = demandArray.get(i).getFunctions()[k].id()-1;
//							int f2= demandArray.get(i).getFunctions()[k+1].id()-1;
//							GRBLinExpr exp = new GRBLinExpr();								
//							exp.addTerm(1, x1[i][f1][j]);
//							exp.addTerm(1, x1[i][f2][j]);							
//							String st = "i3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//							model.addConstr(exp, GRB.LESS_EQUAL, 1, st);
//						}
//					}
	
				
//				for (int i=0;i<demandArray.size();i++)
//					for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//						for(int j1=0;j1<n;j1++)
//							for(int j2=0;j2<n;j2++)
//							{
//								if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//								{
//									GRBLinExpr exp = new GRBLinExpr();								
//									exp.addTerm(1, phi[i][k][j1][j2]);
//									String st = "i4["+(i)+ "]["+(k)+ "]["+(j1+1)+"]["+(j2+1)+  "]";
//									model.addConstr(exp, GRB.GREATER_EQUAL, 0, st);
//								}
//								
//							}
//				for (int i=0;i<demandArray.size();i++)
//				{
//					GRBLinExpr exp = new GRBLinExpr();	
//					int source = demandArray.get(i).sourceS()-1;
//					for(int j2=0;j2<n;j2++)
//					{
//						
//						if(source!=j2 && g.getEdgeWeight(source+1, j2+1)>0)
//						{
//														
//							exp.addTerm(1, phi[i][0][source][j2]);
//							
//						}
//						
//					}
//					String st = "i5["+(i)+ "][0]["+(source+1)+  "]";
//					model.addConstr(exp, GRB.EQUAL, 1, st);
//				}
						
				
//			
				//Eq (12)
				for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							int source = demandArray.get(i).sourceS();
							//if(source != j+1)
							//{
								GRBLinExpr exp = new GRBLinExpr();								
								exp.addTerm(1, x1[i][k][j]);
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp.addTerm(-1, y1[i][j1][j]);
								String st = "k1["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
								exp=null;
								GRBLinExpr exp1 = new GRBLinExpr();		
								for(int j1=0;j1<n;j1++)
									if(g.getEdgeWeight(j1+1, j+1)>0)
										exp1.addTerm(1, y1[i][j1][j]);
								st = "k2["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
								model.addConstr(exp1, GRB.LESS_EQUAL, 1, st);
								exp1=null;
							//}	
//							else
//							{
//								GRBLinExpr exp = new GRBLinExpr();								
//								exp.addTerm(1, x1[i][k][j]);
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp.addTerm(-1, y1[i][j][j1]);
//								String st = "k3["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp, GRB.LESS_EQUAL, 0, st);
//								exp=null;
//								GRBLinExpr exp1 = new GRBLinExpr();		
//								for(int j1=0;j1<n;j1++)
//									if(g.getEdgeWeight(j+1, j1+1)>0)
//										exp1.addTerm(1, y1[i][j][j1]);
//								st = "k4["+(i)+ "]["+(k)+ "]["+(j+1)+  "]";
//								model.addConstr(exp1, GRB.EQUAL, 1, st);
//								exp1=null;
//							}
							
						}
			
				for (int i=0;i<demandArray.size();i++)
				{
					int desti = demandArray.get(i).destinationS();
					int source = demandArray.get(i).sourceS();
					GRBLinExpr expr13= new GRBLinExpr();
					for (int j1=0;j1<n;j1++)
					{
						if(g.getEdgeWeight(source, j1+1)>0)
							expr13.addTerm(1, y1[i][source-1][j1]);
//						if(g.getEdgeWeight(j1+1, source)>0)
//							expr13.addTerm(-1, y1[i][j1][source-1]);
						if(g.getEdgeWeight(j1+1, desti)>0)
							expr13.addTerm(-1, y1[i][j1][desti-1]);
						/*if(g.getEdgeWeight(desti, j1+1)>0)
							expr13.addTerm(1, y1[i][desti-1][j1]);*/
					}
					String st = "sd["+(i)+  "]";
					model.addConstr(expr13, GRB.EQUAL, 0, st);
					expr13=null;
				}
				System.gc();
				
				
				
				
			
				
				// Optimize model
				try {
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'C');
					    			//}
					    		}
					
//					for (int i=0;i<demandArray.size();i++)
//						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//							for(int j1=0;j1<n;j1++)
//								for(int j2=0;j2<n;j2++)
//								{
//									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//										//if(j1!=j2)
//									//{
//					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'C');
//									//}
//								}
					
					
					model.update();
					model.optimize();
					
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
						{
							double _val = x1[i][k][j].get(GRB.DoubleAttr.X);
							x1[i][k][j].set(GRB.DoubleAttr.LB,_val );
							x1[i][k][j].set(GRB.DoubleAttr.UB, _val);
						}
					
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			//if(g.getEdgeWeight(j1+1, j2+1)>0)
					    			//{
					    				y1[i][j1][j2].set(GRB.CharAttr.VType, 'B');
					    			//}
					    		}
					
//					for (int i=0;i<demandArray.size();i++)
//						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
//							for(int j1=0;j1<n;j1++)
//								for(int j2=0;j2<n;j2++)
//								{
//									//if(j1!=j2 && g.getEdgeWeight(j1+1, j2+1)>0)
//										//if(j1!=j2)
//									//{
//					    				phi[i][k][j1][j2].set(GRB.CharAttr.VType, 'B');
//									//}
//								}
					System.out.println("Run optimization again....");
					model.update();
					
					model.optimize();
					//model.write("model1.lp");
					out.write("Solution for the problem:");
					out.newLine();
				
					int optimstatus = model.get(GRB.IntAttr.Status); 
					if (optimstatus == GRB.Status.OPTIMAL) 
					{ 
						//r_min= r.get(GRB.DoubleAttr.X);
						value_final = obj.getValue();
						out.write("Objective optimal Value: "+obj.getValue());
						maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
						maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
						_gap = model.get(GRB.DoubleAttr.MIPGap);
						_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
						
						_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
						out.newLine();
						for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			if(g.getCap(j+1)>leafCapacity)
						    				SpineCount ++;
						    			}
						    		}
						for(int i = 0; i < demandArray.size(); i++) 
						    for(int j1 = 0; j1 < n; j1++)
						    	for(int j2 = 0; j2 < n; j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						for (int i=0;i<demandArray.size();i++)
							for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
								for(int j1=0;j1<n;j1++)
									for(int j2=0;j2<n;j2++)
						    		{	
						    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
						    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			}
						    		}
						out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
		    			out.newLine();
				
					 } else if (optimstatus == GRB.Status.INF_OR_UNBD) 
					 	{ 
					        System.out.println("Model is infeasible or unbounded"); 
					        return;
					 	} else if (optimstatus == GRB.Status.INFEASIBLE) 
					        	{ 
							        System.out.println("Model is infeasible AAAAAAAAAAAAAA"); 
							        return; 
					        	} else if (optimstatus == GRB.Status.INTERRUPTED)
					        	{
					        		//r_min= r.get(GRB.DoubleAttr.X);
					        		maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
									maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					        		value_final = obj.getValue();
					        		_gap = model.get(GRB.DoubleAttr.MIPGap);
									_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
									
									_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
					        		out.write("Objective interrupt Value: "+obj.getValue());
									out.newLine();
									for(int i = 0; i < demandArray.size(); i++) 
									for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
										for(int j = 0; j < n; j++)
								    		{	
								    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
								    			{
								    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
								    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
								    			out.newLine();
								    			if(g.getCap(j+1)>leafCapacity)
								    				SpineCount ++;
								    			}
								    		}
									for (int i=0;i<demandArray.size();i++)
										for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
											for(int j1=0;j1<n;j1++)
												for(int j2=0;j2<n;j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									for(int i = 0; i < demandArray.size(); i++) 
									    for(int j1 = 0; j1 < n; j1++)
									    	for(int j2 = 0; j2 < n; j2++)
									    		{	
									    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
									    			{
									    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
									    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
									    			out.newLine();
									    			}
									    		}
									out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
					    			out.newLine();
					        		
					        	}
					
					 else
					 {
						 //r_min= r.get(GRB.DoubleAttr.X);
						 value_final = obj.getValue();
						 out.write("Objective feasible Value: "+obj.getValue());
						 out.newLine();
						 maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
							maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
							
							_gap = model.get(GRB.DoubleAttr.MIPGap);
							_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
							
							_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
							for(int i = 0; i < demandArray.size(); i++) 
							for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
								for(int j = 0; j < n; j++)
						    		{	
						    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
						    			{
						    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
						    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
						    			out.newLine();
						    			if(g.getCap(j+1)>leafCapacity)
						    				SpineCount ++;
						    			}
						    		}
							for (int i=0;i<demandArray.size();i++)
								for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
									for(int j1=0;j1<n;j1++)
										for(int j2=0;j2<n;j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							for(int i = 0; i < demandArray.size(); i++) 
							    for(int j1 = 0; j1 < n; j1++)
							    	for(int j2 = 0; j2 < n; j2++)
							    		{	
							    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
							    			{
							    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
							    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
							    			out.newLine();
							    			}
							    		}
							out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
			    			out.newLine();
							
					  }
				
					
				} catch (Exception e) {
					//r_min= r.get(GRB.DoubleAttr.X);
					value_final = obj.getValue();
					out.write("Objective interrupt Value: "+obj.getValue());
					out.newLine();
					maxLinkLoad = r_l.get(GRB.DoubleAttr.X);
					maxNodeLoad= r_n.get(GRB.DoubleAttr.X);
					
					_gap = model.get(GRB.DoubleAttr.MIPGap);
					_nodeBB = model.get(GRB.DoubleAttr.NodeCount);
					
					_acceptNo = (value_final + maxLinkLoad + maxNodeLoad)*demandArray.size()/10;
					for(int i = 0; i < demandArray.size(); i++) 
					for(int k = 0; k < demandArray.get(i).getFunctions().length; k++)
						for(int j = 0; j < n; j++)
				    		{	
				    			if(x1[i][k][j].get(GRB.DoubleAttr.X)>0)
				    			{
				    			out.write(x1[i][k][j].get(GRB.StringAttr.VarName)
				    					+ " : " +x1[i][k][j].get(GRB.DoubleAttr.X));
				    			out.newLine();
				    			if(g.getCap(j+1)>leafCapacity)
				    				SpineCount ++;
				    			}
				    		}
					for (int i=0;i<demandArray.size();i++)
						for(int k=0;k<demandArray.get(i).getFunctions().length;k++)
							for(int j1=0;j1<n;j1++)
								for(int j2=0;j2<n;j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&phi[i][k][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(phi[i][k][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +phi[i][k][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					for(int i = 0; i < demandArray.size(); i++) 
					    for(int j1 = 0; j1 < n; j1++)
					    	for(int j2 = 0; j2 < n; j2++)
					    		{	
					    			if(g.getEdgeWeight(j1+1, j2+1)>0&&y1[i][j1][j2].get(GRB.DoubleAttr.X)>0)
					    			{
					    			out.write(y1[i][j1][j2].get(GRB.StringAttr.VarName)
					    					+ " : " +y1[i][j1][j2].get(GRB.DoubleAttr.X));
					    			out.newLine();
					    			}
					    		}
					out.write("Number of Spine: "+ SpineCount*1.0/(m1*_acceptNo));
	    			out.newLine();
					
	
				}
				spineRatio = SpineCount*1.0/(m1*_acceptNo);
				System.out.println("Spine Ratio = "+ spineRatio);
					model.dispose();
				env.dispose();
				System.gc();
			
				} catch(GRBException e3){			
					System.out.println("Error code1: " + e3.getErrorCode() + ". " +
							e3.getMessage());
					System.out.print("This problem can't be solved");
					
					
					}
			} catch ( IOException e1 ) {
					e1.printStackTrace();
					} finally {
						if ( out != null )
							try {
								out.close();
								} catch (IOException e) {
									e.printStackTrace();}
						}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
	
	
	
	
	}
	public static void mainCo(String folderName)
	{
		//Cover
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output1309/output_Callback1.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							ReadInputFile(file.getPath());
							//ReadInput(file.getPath());
							System.out.println("Gurobi adding Flow cover solving.....: "+ tau);
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/Cover_"+tau+"_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							final long startTime = System.currentTimeMillis();
							//Cover(str);
							Cover_new(str);
							_duration = System.currentTimeMillis() - startTime;
								out1.write(" "+m + " " +d +" "+n+" "+ tau+ " "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad + " "+ s0Size + " "+noCoverFlow+" "+ _gap +" "+_nodeBB+" "+ _acceptNo.intValue()+" "+ _duration);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	}
	public static void mainCoverOct(String folderName)
	{
		//Cover
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output/output_CoverOct.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							ReadInputFile(file.getPath());
							//ReadInput(file.getPath());
							System.out.println("Gurobi OCtober: ");
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/CoverOct_"+tau+"_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							value_final =0;
							s0Size=0;
							noCoverFlow=0;
							_gap = 0;
							_nodeBB =0;
							_acceptNo = 0.0;
							finalRunTime =0;
							final long startTime = System.currentTimeMillis();
							//Cover(str);
							Cover_Oct(str);
							_duration = System.currentTimeMillis() - startTime;
							System.out.println(" "+m + " " +d +" "+n+" "+ tau+ " "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad + " "+ s0Size + " "+noCoverFlow+" "+ _gap +" "+_nodeBB+" "+ _acceptNo.intValue()+" "+ _duration);
								out1.write(" "+m + " " +d +" "+n+" "+ tau+ " "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad + " "+ s0Size + " "+noCoverFlow+" "+ _gap +" "+_nodeBB+" "+ _acceptNo.intValue()+" "+ _duration);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	}
	public static void mainNew(String folderName)
	{
		//giai voi gurobi
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output1309/output_Gurobi_dynamic.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							ReadInputFile(file.getPath());
							//ReadInput(file.getPath());
							System.out.println("Gurobi without adding Flow cover solving.....");
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/newGurobi_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							//Model_congestion(str);
							final long startTime = System.currentTimeMillis();
							dynamic_model(str);
							_duration = System.currentTimeMillis() - startTime;
								out1.write(" "+m + " " +d +" "+n+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad + " "+ _gap +" "+_nodeBB+" "+ _acceptNo.intValue()+" "+ _duration);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	}
	public static void mainGu(String folderName) {//giai voi gurobi
		BufferedWriter out1 = null;
		//currentTime=Double.parseDouble(args[0]);
		//maxNode = Double.parseDouble(args[0]);
		//String folderName = args[0];
		File dir = new File(folderName);
		String[] extensions = new String[] { "txt" };
		try {
			System.out.println("Getting all .txt in " + dir.getCanonicalPath()
					+ " including those in subdirectories");
		} catch (IOException e) {
			e.printStackTrace();
		}
		List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
		String chuoi1= "./output/output_Gurobi.txt";
		File _f = new File(chuoi1 );
		String str="";
		try {
			out1 = new BufferedWriter(new FileWriter(_f,true));
			for (File file : files) {
				try {
					System.out.println("file: " + file.getCanonicalPath());
					ReadInputFile(file.getPath());
					//ReadInput(file.getPath());
					str=file.getName(); 
					///TODO
					String chuoi2= "./resultFiles/Gurobi_";
					str = chuoi2+str;
					//str = str.replace("in",chuoi2 );
					out1.write(str);
					_duration=0;
					maxLinkLoad=0.0;
					maxNodeLoad=0;
					value_bandwidth =0;
					value_final =0;
					s0Size=0;
					noCoverFlow=0;
					_gap = 0;
					_nodeBB =0;
					_acceptNo = 0.0;
					finalRunTime =0;
					final long startTime = System.currentTimeMillis();
					//Model_Minh(str);
					dynamic_model(str);
					_duration = System.currentTimeMillis() - startTime;
					out1.write(" "+m + " " +d +" "+n+" "+ tau+ " "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad + " "+ s0Size + " "+noCoverFlow+" "+ _gap +" "+_nodeBB+" "+ _acceptNo.intValue()+" "+ _duration);
						out1.newLine();
					
					
					
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
		} catch ( IOException e1 ) {
			e1.printStackTrace();
			} 
		try {
			out1.close();
		} catch (IOException e) {
			// TODO Auto-generated scatch block
			e.printStackTrace();
		}	
		
    }
	
	public static void mainHeu3_1(String folderName)
	{

System.out.println("Heuristic 3 phay");
		//giai voi heuristic
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output/output_Heu31.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							ReadInputFile(file.getPath());
							//ReadInput(file.getPath());
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/Heu31_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							//EditHeuristic(str);
							final long startTime = System.currentTimeMillis();
							Heu3_1(str);
							_duration = System.currentTimeMillis() - startTime;
							
								out1.write(" "+m + " " +d +" "+n+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad +" "+ _acceptNo.intValue()+" "+ _duration);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	
	
	}
	
	public static void mainHeu5(String folderName)
	{

		System.out.println("Heuristic 5");
		//giai voi heuristic
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output/output_Heu5.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							ReadInputFile(file.getPath());
							//ReadInput(file.getPath());
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/Heu5_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							//EditHeuristic(str);
							final long startTime = System.currentTimeMillis();
							Heu5(str);
							_duration = System.currentTimeMillis() - startTime;
								out1.write(" "+m + " " +d +" "+n+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad +" "+ _acceptNo.intValue()+" "+ _duration);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	
	
	}
	public static void mainHeu4(String folderName)
	{
		System.out.println("Heuristic 4");
		//giai voi heuristic
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output/output_Heu4.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							//ReadFileAndUpdate(file.getPath());
							ReadInputFile(file.getPath());
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/Heu4_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							//EditHeuristic(str);
							final long startTime = System.currentTimeMillis();
							Heu4(str);
							_duration = System.currentTimeMillis() - startTime;
								out1.write(" "+m + " " +d +" "+n+" "+_capChanging+" "+ _noLinkAdding+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad +" "+ _acceptNo.intValue()+" "+ _duration + " "+ spineRatio);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	
	}
	public static void mainNewHeu(String folderName)
	{
		//giai voi heuristic
				BufferedWriter out1 = null;
				//currentTime=Double.parseDouble(args[0]);
				//maxNode = Double.parseDouble(args[0]);
				//String folderName = args[0];
				File dir = new File(folderName);
				String[] extensions = new String[] { "txt" };
				try {
					System.out.println("Getting all .txt in " + dir.getCanonicalPath()
							+ " including those in subdirectories");
				} catch (IOException e) {
					e.printStackTrace();
				}
				List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
				String chuoi1= "./output/output_newheu.txt";
				File _f = new File(chuoi1 );
				String str="";
				try {
					out1 = new BufferedWriter(new FileWriter(_f,true));
					for (File file : files) {
						try {
							System.out.println("file: " + file.getCanonicalPath());
							//ReadFileAndUpdate(file.getPath());
							ReadInputFile(file.getPath());
							
							str=file.getName(); 
							///TODO
							String chuoi2= "./resultFiles/newheu_";
							str = chuoi2+str;
							//str = str.replace("in",chuoi2 );
							out1.write(str);
							_duration=0;
							maxLinkLoad=0.0;
							maxNodeLoad=0;
							value_bandwidth =0;
							//EditHeuristic(str);
							final long startTime = System.currentTimeMillis();
							newHeu(str);
							_duration = System.currentTimeMillis() - startTime;
								out1.write(" "+m + " " +d +" "+n+" "+_capChanging+" "+ _noLinkAdding+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad +" "+ _acceptNo.intValue()+" "+ _duration+ " "+ spineRatio);
								out1.newLine();
							
							
							
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
					
				} catch ( IOException e1 ) {
					e1.printStackTrace();
					} 
				try {
					out1.close();
				} catch (IOException e) {
					// TODO Auto-generated scatch block
					e.printStackTrace();
				}	
				
		    
	}
	public static void mainHeu(String folderName) {//giai voi heuristic
		BufferedWriter out1 = null;
		//currentTime=Double.parseDouble(args[0]);
		//maxNode = Double.parseDouble(args[0]);
		//String folderName = args[0];
		File dir = new File(folderName);
		String[] extensions = new String[] { "txt" };
		try {
			System.out.println("Getting all .txt in " + dir.getCanonicalPath()
					+ " including those in subdirectories");
		} catch (IOException e) {
			e.printStackTrace();
		}
		List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
		String chuoi1= "./output/output_heu.txt";
		File _f = new File(chuoi1 );
		String str="";
		try {
			out1 = new BufferedWriter(new FileWriter(_f,true));
			for (File file : files) {
				try {
					System.out.println("file: " + file.getCanonicalPath());
					//ReadFileAndUpdate(file.getPath());
					
					ReadInputFile(file.getPath());
					str=file.getName(); 
					///TODO
					String chuoi2= "./resultFiles/heu_";
					str = chuoi2+str;
					//str = str.replace("in",chuoi2 );
					out1.write(str);
					_duration=0;
					maxLinkLoad=0.0;
					maxNodeLoad=0;
					value_bandwidth =0;
					//EditHeuristic(str);
					final long startTime = System.currentTimeMillis();
					Heuristic(str);
					_duration = System.currentTimeMillis() - startTime;
						out1.write(" "+m + " " +d +" "+n+" "+_capChanging+" "+ _noLinkAdding+" "+value_final+" "+ maxLinkLoad+" "+maxNodeLoad +" "+ _acceptNo.intValue()+" "+ _duration+ " "+ spineRatio);
						out1.newLine();
					
					
					
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
		} catch ( IOException e1 ) {
			e1.printStackTrace();
			} 
		try {
			out1.close();
		} catch (IOException e) {
			// TODO Auto-generated scatch block
			e.printStackTrace();
		}	
		
    }

	
	
	
public static void mainInput() {
	//UtilizeFunction.CreateInput("./lib/createTOPO.txt");
	//UtilizeFunction.CreateInput("./lib/realworld.txt","data_130917");
	UtilizeFunction.randomLeafSpineTopo("./lib/LeafSpineTopo.txt");
}


public static double exponentialRandom(double mu)
{
	Random r = new Random();
	ExponentialGenerator ex = new ExponentialGenerator(mu, r);
	System.out.println("Random value: "+ ex.nextValue());
	return ex.nextValue();
	
}
public static double poissonRandom(double lamda)
{
	Random r = new Random();
	PoissonGenerator pois = new PoissonGenerator(lamda, r);
	System.out.println("Random poisson value: "+ pois.nextValue());
	return pois.nextValue();
}

public static double nextTime(double rateParameter)
{
	Random r = new Random();
	return -Math.log(1.0 - r.nextDouble()) / rateParameter;
}

public static void Simulation(double lamda,double mu,double NumFlow, int idAlg,double timeEvent)
{
	n = g.V();
	Integer[] bandF = new Integer[]{1,1};
	double epsilon = 0.01;
	double X = NumFlow;
	double processingReq =0.05;
	int dem1=0;
	int dem2=0;
	//noFunction=10;
	double now=0.0;
	int index=0;
	link_load= new double[n][n];
	//int id_temp=-1;
	ArrayList<Integer> id_temp = new ArrayList<>();
	ArrayList<nOldDemand> processingLst = new ArrayList<>();
	int acceptNoLst = 0;
	double avgLenLst = 0.0;
	double maximumLinkLoad = 0.0;
	double maximumNodeLoad = 0.0;
	double runTime =0.0;
	
	double timeCheck = timeEvent;
	//random topology -> nGraph 
	
	//random 10000 flows
    int idFlow=0;
    int flows=0;
    MyGraph g_edit= new MyGraph(g.K, g.w);
    demandArray = new ArrayList<>();
   
		while (true)
	    {
			idFlow++;
			flows++;
			flag =0;
			double processTime = exponentialRandom(mu);
			Demand _d = new Demand(idFlow,now,functionArr,g.V(),g,bandF); 
			_d.setProcessingTime(processTime);
			demandArray.add(_d);
	    	System.out.println("Flow: "+ index+":"+now+":"+ _d.sourceS()+","+_d.destinationS() );
	    		fl = false;
	    		id_temp= new ArrayList<>();
	    		
	    		
	    		if (now>timeCheck || now > X)
	    		{
	    			g_edit= new MyGraph(g.K, g.w);
		    		if(processingLst!=null && processingLst.size()>0)
			    	{
			    		for(nOldDemand _old: processingLst)
			    		{
			    			
			    			if(now > (_old.GetArrivalTime()+_old.GetProcessTime()))
			    			{
			    				id_temp.add(processingLst.indexOf(_old));						
			    			}
			    			else
			    			{
			    				ArrayList<Integer> path= _old.Get_path();
			    				
			    					for (int _node=0;_node<path.size()-1;_node++)
									{
			    						if(path.get(_node)!=path.get(_node+1))
			    						{
			    							int w_temp= g_edit.getEdgeWeight(path.get(_node), path.get(_node+1))-_old.GetBandwidth();
											g_edit.setEdgeWeight(path.get(_node), path.get(_node+1),w_temp );
				    						if(g.getEdgeWeight(path.get(_node), path.get(_node+1))>0)
				    							link_load[path.get(_node)-1][path.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(path.get(_node), path.get(_node+1));
				    						
				    						
			    						}		    						
			    						
									}
			    					
			    				ArrayList<Integer> fLoc = _old.Get_fLoc();
			    				Function[] fSet = _old.getFunc();
			    				for(int j=0;j<fLoc.size();j++)
			    				{
			    					int mul = fSet[j].getReq();
	    							int c_cap =  g_edit.getCap(fLoc.get(j))-mul;
									g_edit.setCap(fLoc.get(j),c_cap );
			    				}
			    				
			    			}
			    		}
			    	}
		    		else
		    			processingLst= new ArrayList<>();
		    		if(id_temp.size()>0)
		    		{
		    			for (int j=0;j<id_temp.size();j++)
		    				processingLst.remove(id_temp.get(j));
		    		}
	    			
	    			timeCheck +=timeEvent;
	    			//chay giai thuat
	    			final long startTime = System.currentTimeMillis();
	    			
		    		switch (idAlg) {
		    		//truyen vao mot tap cac demand and g_edit
					case 1:
						Heuristic(demandArray,g_edit);
						break;
					case 2:
						dynamic_model(demandArray,g_edit);						
						break;
					case 3:
						dynamic_heu3(demandArray,g_edit);						
						break;
					case 4:
						dynamic_heu4(demandArray,g_edit);						
						break;
					case 5:
						dynamic_heu5(demandArray,g_edit);						
						break;
					default:
						break;
					}
		    		_duration = System.currentTimeMillis() - startTime;
//		    		if(now>warmup)
//		    		{
//		    			flows++;
		    			runTime+=_duration;
//		    		}
		    		
		    		//add cac demand vao trong tap cac demand dang process
		    		acceptNoLst+=demandArray.size()-_solSet.getBlocking();
		    		
		    		for(int idD=0;idD<_solSet.getDemand().size();idD++)
		    		{
		    			//tap cac demand can add
		    			//if(now>warmup)
	    				//{
	    					
			    			
	    				//}
		    			Demand _dTemp = _solSet.getDemand().get(idD);
		    			avgLenLst+=_solSet.getPath().get(idD).size();
		    			
		    			nOldDemand _old = new nOldDemand(_dTemp.idS(), _dTemp.arrivalTimeS(), _dTemp.processingTimeS(), _dTemp.bwS(), _solSet.getPath().get(idD), _solSet.getFunLoc().get(idD),_dTemp.getRate(),_dTemp.getFunctions());
			    		processingLst.add(_old);	    			
		    			
		    		}   
		    		if(maxLinkLoad>maximumLinkLoad)
		    			maximumLinkLoad = maxLinkLoad;
		    		if(maxNodeLoad>maximumNodeLoad)
		    			maximumNodeLoad = maxNodeLoad;
		    	
		    	
		    	demandArray = new ArrayList<>();
	    	}
	    		index++;
		    	//System.out.println("number of processed flows: "+ index);
		    	now = now+ nextTime(lamda);
		    	if(now > X)
		    	{
			    	finalblocking= 1.0 - acceptNoLst*1.0/flows;
			    	finallengLst=avgLenLst/acceptNoLst;
			    	finalRunTime= runTime/flows;
		    		break;
		    	}
	    		
	    		
	    		
	    }
}

public static void main(String[] args)//opt
{

	
	String folderName = args[0];
	int p = Integer.parseInt(args[1]);
	double alpha = Double.parseDouble(args[2]);
	String fileMain =  args[3];
	tau = Integer.parseInt(args[4]);
	_capChanging = Integer.parseInt(args[5]);
	_noLinkAdding= Integer.parseInt(args[6]);
	switch (fileMain) {
	case "Input":
		mainInput();
		break;
	case "Gurobi":
		mainGu(folderName);
		break;
	case "BasedHeu":
		mainBasedHeu(folderName, p, alpha);
		break;
	case "Heu":
		mainHeu(folderName);
		break;
	case "Cover":
		mainCo(folderName);
		break;
	case "new":
		mainNew(folderName);
		break;
	case "CoverOct":
		mainCoverOct(folderName);
		break;
	case "newHeu":
		mainNewHeu(folderName);
		break;
	case "Heu4":
		mainHeu4(folderName);
		break;
	case "Heu3":
		mainHeu3_1(folderName);
		break;
	case "Heu5":
		mainHeu5(folderName);
		break;
	default:
		break;
	}

	
}
public static void mainSim(String args[])//simulation
{
	
	String  folderName= args[0];
	double lamda= Double.parseDouble(args[1]);
	double mu = Double.parseDouble(args[2]);
	double NumFlow=Double.parseDouble(args[3]);
	int idAlg=Integer.parseInt(args[4]);
	double timeEvent=Double.parseDouble(args[5]);
	tau = 1;
	//giai voi heuristic
			BufferedWriter out1 = null;
			//currentTime=Double.parseDouble(args[0]);
			//maxNode = Double.parseDouble(args[0]);
			//String folderName = args[0];
			File dir = new File(folderName);
			String[] extensions = new String[] { "txt" };
			try {
				System.out.println("Getting all .txt in " + dir.getCanonicalPath()
						+ " including those in subdirectories");
			} catch (IOException e) {
				e.printStackTrace();
			}
			List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);
			String chuoi2="";
			if(idAlg==1)
				chuoi2= "Heu_";
			if(idAlg==2)
				chuoi2="Optimal_";
			if(idAlg==3)
				chuoi2="Heu3_";
			if(idAlg==4)
				chuoi2="Heu4_";
			if(idAlg==5)
				chuoi2="Heu5_";
			String chuoi1= "./output/output_"+chuoi2+"dynamic.txt";
			File _f = new File(chuoi1 );
			String str="";
			try {
				out1 = new BufferedWriter(new FileWriter(_f,true));
				for (File file : files) {
					try {
						System.out.println("file: " + file.getCanonicalPath());
						ReadInputFile(file.getPath());
						//ReadInput(file.getPath());
						str=file.getName(); 
						///TODO
						
						str = chuoi2+str;
						//str = str.replace("in",chuoi2 );
						out1.write(str);
						_duration=0;
						maxLinkLoad=0.0;
						maxNodeLoad=0;
						value_bandwidth =0;
						//EditHeuristic(str);
						
						Simulation(lamda,mu,NumFlow,idAlg,timeEvent);
							out1.write(lamda+" "+mu+" "+ maxLinkLoad+" "+maxNodeLoad+ " "+ finalblocking+" "+ finallengLst+ " "+finalRunTime+" ");
							out1.newLine();
						
						
						
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
				
			} catch ( IOException e1 ) {
				e1.printStackTrace();
				} 
			try {
				out1.close();
			} catch (IOException e) {
				// TODO Auto-generated scatch block
				e.printStackTrace();
			}	
			
	    
}

}