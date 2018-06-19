import java.util.ArrayList;


public class nOldDemand {
	//source, destination,bandwidth,arrival time,process time,set of function (number of function),v_sol,f_sol
    private int id;//id of demand
    private int bw;//bandwidth
    private ArrayList<Pair> funLoc;
    private ArrayList<Integer> fLoc;
    private Function[] f;
	//private ArrayList<ArrayList<Integer>> path;
    private ArrayList<Integer> path;
    private double arrivalTime;
    private double processtime;
    private double processReq;
 public nOldDemand()
 {	
	 this.id=-1;
 }

//    public nOldDemand(int IdS,double ArrivalTime,double ProcessTime,int BwS,ArrayList<Integer> Path,ArrayList<Pair> FunLoc,double _processReq) {
//    	this.id = IdS;
//    	this.bw = BwS;
//    	this.arrivalTime = ArrivalTime;
//    	this.processtime = ProcessTime;
//    	 this.path = new ArrayList<>();
//     	this.funLoc=new ArrayList<Pair>();
//     	this.path = Path;
//     	this.funLoc = FunLoc;
//     	this.processReq = _processReq;
//        
//    }
    public nOldDemand(int IdS,double ArrivalTime,double ProcessTime,int BwS,ArrayList<Integer> Path,ArrayList<Integer> FLoc,double _processReq,Function[] _f) {
    	this.id = IdS;
    	this.bw = BwS;
    	this.arrivalTime = ArrivalTime;
    	this.processtime = ProcessTime;
    	 this.path = new ArrayList<>();
     	this.fLoc=new ArrayList<>();
     	this.f = _f;
     	this.path = Path;
     	this.fLoc = FLoc;
     	this.processReq = _processReq;
        
    }
    public int GetID() { return id; }
    public double GetArrivalTime() { return arrivalTime; }
    public double GetProcessTime() { return processtime; }
    public int GetBandwidth() { return this.bw; }
    public double GetProcessReq() { return this.processReq; }
    public ArrayList<Integer> Get_path(){return this.path;}
    public ArrayList<Pair> Get_funLoc(){return this.funLoc;}
    public ArrayList<Integer> Get_fLoc(){return this.fLoc;}
    public Function[] getFunc(){return this.f;}
    public static void main(String[] args) {
    }

}