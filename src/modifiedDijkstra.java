import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;

import org.jgrapht.WeightedGraph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultDirectedWeightedGraph;
import org.jgrapht.graph.DefaultWeightedEdge;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.Graph;

/**
 * @author Anupam
 *
 */
public class modifiedDijkstra{

 //private DirectedGraph<Vertex, String> g;
private DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> g1;
//=new DefaultDirectedWeightedGraph<Vertex,DefaultWeightedEdge>(DefaultWeightedEdge.class);;
 private Set<List<Vertex>> allShortestPaths;
 
 public modifiedDijkstra(DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> _g1){
this.g1= _g1;
 }
 
 private Vertex getSourceFromId(Integer sourceId){
 Collection<Vertex> vertices = g1.vertexSet();
 for (Iterator<Vertex> iterator = vertices.iterator(); iterator.hasNext();) {
 Vertex vertex = (Vertex) iterator.next();
 if(vertex.getId() == sourceId)
 return vertex;
 }
 
 return null;
 }
 
 /**
  * Computes all shortest paths to all the vertices in the graph
  * using the Dijkstra's shortest path algorithm.
  * 
  * @param sourceId : Starting node from which to find the shortest paths.
  */
 public void computeAllShortestPaths(Integer sourceId){
	 for(Vertex v:g1.vertexSet())
	 {
		 v.sourceDistance=0;
	 }
 Vertex source = getSourceFromId(sourceId);
 if(source==null)
	 return;
 source.sourceDistance = Double.MAX_VALUE;
        PriorityQueue<Vertex> vertexQueue = new PriorityQueue<Vertex>();
       vertexQueue.add(source);
       List<Vertex> prev = null;

 while (!vertexQueue.isEmpty()) {
 Vertex u = vertexQueue.poll();
 double minWeight = 0;
 
 Collection<Vertex> neighbs= new ArrayList<Vertex>();
for (DefaultWeightedEdge e:g1.edgeSet())
{
	Vertex v1 = g1.getEdgeSource(e);
	Vertex v2 = g1.getEdgeTarget(e);
	if(u==v1)
	{
		neighbs.add(v2);
		if(g1.getEdgeWeight(e)>minWeight)
			minWeight = g1.getEdgeWeight(e);
	}
}

for (Iterator<Vertex> iterator = neighbs.iterator(); iterator.hasNext();) 
{
	 Vertex nv = (Vertex) iterator.next();
	 prev = nv.getPrev();
	 DefaultWeightedEdge e = g1.getEdge(u, nv);
	 double weight = g1.getEdgeWeight(e);
	 double distanceThroughU = -1;
	 if(u.sourceDistance < weight)
		 distanceThroughU = u.sourceDistance;
	 else
		 distanceThroughU = weight;
	 //if(distanceThroughU>weight)
		 //distanceThroughU = weight;
	 if (distanceThroughU > nv.sourceDistance ) 
	 {
			 vertexQueue.remove(nv);
			 nv.sourceDistance = distanceThroughU;
			 nv.setPrevious(u);
			 vertexQueue.add(nv);
			 prev = new ArrayList<Vertex>();
			 prev.add(u);
			 nv.setPrev(prev);
		 
	}
	 else if(distanceThroughU == nv.sourceDistance)
	 {
		 if(prev != null)
			 prev.add(u);
		 else 
		 {
			 prev = new ArrayList<Vertex>();
			 prev.add(u);
			 //nv.setPrev(prev);
			 
		 }
		 nv.setPrev(prev);
		 
	}
//	 else
//	 {
//		 vertexQueue.remove(nv);
//		 nv.sourceDistance = weight;
//		 nv.setPrevious(u);
//		 vertexQueue.add(nv);
//		 prev = new ArrayList<Vertex>();
//		 prev.add(u);
//		 nv.setPrev(prev);
//	 }
}
 }
 }
 
 /**
  * @param target
  * @return A List of nodes in order as they would appear in a shortest path.
  * (There can be multiple shortest paths present. This method returns just one
  * of those paths.)
  */
 public List<Vertex> getShortestPathTo(Vertex target){
        List<Vertex> path = new ArrayList<Vertex>();
        for (Vertex vertex = target; vertex != null; vertex = vertex.getPrevious())
            path.add(vertex);
        Collections.reverse(path);
        return path;
    }
 
 /**
  * @param target
  * @return A set of all possible shortest paths from the source to the given
  * target.
  */
 public Set<List<Vertex>> getAllShortestPathsTo(Vertex target){
 allShortestPaths = new HashSet<List<Vertex>>();
 
 getShortestPath(new ArrayList<Vertex>(), target);
 
 return allShortestPaths;
 }
 
 /**
  * Recursive method to enumerate all possible shortest paths and
  * add each path in the set of all possible shortest paths.
  * 
  * @param shortestPath
  * @param target
  * @return
  * 
  */
 private List<Vertex> getShortestPath(List<Vertex> shortestPath, Vertex target){
 List<Vertex> prev = target.getPrev();
 List<Vertex> tempPath = new ArrayList<>();
 for(int i=0;i<shortestPath.size();i++)
	 tempPath.add(shortestPath.get(i));
 if(prev == null){
 //shortestPath.add(target);
 tempPath = new ArrayList<>();
 for(int i=0;i<shortestPath.size();i++)
	 tempPath.add(shortestPath.get(i));
 tempPath.add(target);
 Collections.reverse(tempPath); 
 allShortestPaths.add(tempPath);


 } else {
 List<Vertex> updatedPath = new ArrayList<Vertex>(shortestPath);
 updatedPath.add(target);
 
 for (Iterator<Vertex> iterator = prev.iterator(); iterator.hasNext();) {
 Vertex vertex = (Vertex) iterator.next();
 getShortestPath(updatedPath, vertex);
 }
 }
 return shortestPath;
 }
}