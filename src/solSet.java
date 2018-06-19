import java.util.ArrayList;




public class solSet {
	private ArrayList<Demand> d;
	private ArrayList<ArrayList<Integer>> funLoc = new ArrayList<>();	
	//thuc hien o day
       
	private  ArrayList<ArrayList<Integer>> sol= new ArrayList<>();
    private int blocking;
    // empty graph with V vertices
    public solSet(ArrayList<Demand> _d,ArrayList<ArrayList<Integer>> sol_p, ArrayList<ArrayList<Integer>> _funLoc,int _blocking)
    {
    	d = _d;
        sol= sol_p;
        funLoc = _funLoc;
        blocking = _blocking;
    }   

    // number of vertices and edges
    public ArrayList<ArrayList<Integer>> getPath() { return sol; }
    public ArrayList<ArrayList<Integer>> getFunLoc() { return funLoc; }
    public ArrayList<Demand> getDemand(){return d;}
    public int getBlocking(){return blocking;}

    // test client
    public static void main(String[] args) {
    }

}