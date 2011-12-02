import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.lang.ref.Reference;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Vector;

import org.neo4j.graphdb.GraphDatabaseService;
import org.neo4j.graphdb.Node;
import org.neo4j.graphdb.Relationship;
import org.neo4j.graphdb.RelationshipType;
import org.neo4j.graphdb.Transaction;
import org.neo4j.kernel.EmbeddedGraphDatabase;

class DocInfo {
	public int id;
	public String author;

	public DocInfo(int id, String author) {
		this.id = id;
		this.author = author;
	}
}

class AuthorGraph {
	// author name, author id
	public HashMap<String, Integer> map = new HashMap<String, Integer>();
	public LinkedList<Integer>[] graph;
	public int[] outdegree;
	public double[] score;
	public int count; // author count
	public int rel_count;// relationship count

	public AuthorGraph() {
		this.count = 0;
		this.rel_count = 0;
	}
}

public class NeoGraph {
	public static String DB_PATH;
	public static String DIC_PATH;
	public static String OUT_PATH;
	public static HashMap<String, DocInfo> docs;
	public static AuthorGraph authors;
	public static GraphDatabaseService graphDb;
	public static LinkedList<Integer>[] graph;
	// the map between doc id and author id
	public static LinkedList<Integer> dtoa; 
	public static Node[] node;
	public static double[] score; // the page rank scores
	public static int[] outdegree;
	public static int node_count;
	public static int rel_count;
	public static final double EP = 0.00001;
	public static final int MAX_ITERATION_TIME = 1000;

	/**
	 * @param args
	 */
	private static enum RelTypes implements RelationshipType {
		LINK;
	}

	public static void import_dict() {
		DocInfo doc;
		String path;
		String line;
		String fname;
		String aname;
		int i;
		Integer id;
		BufferedReader br;

		try {
			node_count = 0;
			path = DIC_PATH + "/author_dict.txt";
			br = new BufferedReader(new FileReader(new File(path)));
			while ((line = br.readLine()) != null) {
				if ((i = line.indexOf(".txt,")) == -1) {
					// some format exceptions
					if ((i = line.indexOf("_txt,")) == -1) {
						if ((i = line.indexOf("txt_,")) == -1) {
							System.out.println("oops, index error: " + line);
							continue;
						}
					}
				}
				fname = line.substring(0, i);
				aname = line.substring(i + 5);
				doc = new DocInfo(node_count, aname);
				if (docs.put(fname, doc) != null) {
					System.out.println("oops, collision happens");
				}
				
				if (aname.compareTo("-") != 0) {
					id = authors.map.get(aname);
					if (id == null) {
						dtoa.addLast(authors.count);
						authors.map.put(aname, authors.count);
						authors.count++;
					} else {
						dtoa.addLast(id);
					}
				} else {
					dtoa.addLast(-1);
				}

				node_count++;
			}
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	public static String get_src(String line) {
		int i;

		i = line.indexOf(".txt");
		if (i > 0) {
			return line.substring(0, i);
		}
		return null;
	}

	public static String get_des(String line) {
		int i;

		i = line.indexOf(".txt,");
		if (i != -1) {
			return line.substring(i + 5).replace(' ', '_');
		}
		return null;
	}

	public static void creat_author_graph(String src, String des) {
		int src_id;
		int des_id;

		if (src.compareTo("-") == 0 || des.compareTo("-") == 0) {
			return;
		}
		src_id = authors.map.get(src);
		des_id = authors.map.get(des);

		authors.graph[des_id].add(src_id); // the reversed author graph
		authors.outdegree[src_id]++;
		authors.rel_count++;
	}

	public static void creat_graph() {
		Transaction tx;
		String path;
		String line = "";
		String src;
		String des = "";
		File file;
		BufferedReader br;
		Integer src_id;
		Integer des_id = 0;

		tx = graphDb.beginTx();
		rel_count = 0;
		node = new Node[node_count];
		outdegree = new int[node_count];
		graph = (LinkedList<Integer>[]) new LinkedList[node_count];
		authors.graph = (LinkedList<Integer>[]) new LinkedList[authors.count];
		authors.outdegree = new int[authors.count];
		for (int i = 0; i < node_count; i++) {
			graph[i] = new LinkedList<Integer>();
			node[i] = graphDb.createNode();
			outdegree[i] = 0;
		}
		for (int i = 0; i < authors.count; i++) {
			authors.graph[i] = new LinkedList<Integer>();
			authors.outdegree[i] = 0;
		}
		try {
			// open file
			path = DIC_PATH + "/link_resository.txt";
			file = new File(path);
			if (!file.exists()) {
				System.out.println("file does not exist");
				return;
			}
			br = new BufferedReader(new FileReader(file));
			// create relationships between nodes
			while ((line = br.readLine()) != null) {
				src = get_src(line);
				des = get_des(line);
				if (src == null || des == null) {
					continue;
				}
				if (!(docs.containsKey(src) && docs.containsKey(des))) {
					continue;
				}
				src_id = docs.get(src).id;
				des_id = docs.get(des).id;
				outdegree[src_id]++;
				graph[des_id].addLast(src_id); // the reversed graph
				rel_count++;
				node[src_id].createRelationshipTo(node[des_id], RelTypes.LINK);
				creat_author_graph(docs.get(src).author, docs.get(des).author);
			}
			tx.success();
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			tx.finish();
		}
		graphDb.shutdown();
	}

	public static boolean equal(double a, double b) {
		return a == b ? true : Math.abs(a - b) < EP;
	}

	/*
	 * compute the page rank score
	 */
	public static void pagerank() {
		double d = 0.85; // the damping factor
		double[] new_score = new double[node_count];
		Iterator<Integer> it;
		int id;
		boolean flag;

		score = new double[node_count];
		for (int i = 0; i < node_count; i++) {
			score[i] = 1.0;
		}

		for (int i = 0; i < MAX_ITERATION_TIME; i++) {
			// for each iteration, compute the new page rank score
			for (int j = 0; j < node_count; j++) {
				new_score[j] = (1.0 - d);
				it = graph[j].iterator();
				while (it.hasNext()) {
					id = (Integer) it.next();
					new_score[j] += d * score[id] / (double) outdegree[id];
				}
			}
			// determine to terminate
			flag = true;
			for (int j = 0; j < node_count; j++) {
				if (!equal(new_score[j], score[j])) {
					flag = false;
					break;
				}
			}
			if (flag) {
				System.out.println("Reach the steady state after " + i
						+ " iterations.");
				return;
			}
			// copy the new score[] to score[]
			for (int j = 0; j < node_count; j++) {
				score[j] = new_score[j];
			}
		}
		System.out.println("Reach maximal iteration limitation.");
	}

	public static void author_score() {
		double d = 0.85; // the damping factor
		double[] new_score = new double[node_count];
		Iterator<Integer> it;
		int id;
		boolean flag;

		authors.score = new double[authors.count];
		for (int i = 0; i < authors.count; i++) {
			authors.score[i] = 1.0;
		}

		for (int i = 0; i < MAX_ITERATION_TIME; i++) {
			// for each iteration, compute the new page rank score
			for (int j = 0; j < authors.count; j++) {
				new_score[j] = (1.0 - d);
				it = authors.graph[j].iterator();
				while (it.hasNext()) {
					id = (Integer) it.next();
					new_score[j] += d * authors.score[id]
							/ (double) authors.outdegree[id];
				}
			}
			// determine to terminate
			flag = true;
			for (int j = 0; j < authors.count; j++) {
				if (!equal(new_score[j], authors.score[j])) {
					flag = false;
					break;
				}
			}
			if (flag) {
				System.out.println("Reach the steady state after " + i
						+ " iterations.");
				return;
			}
			// copy the new score[] to score[]
			for (int j = 0; j < authors.count; j++) {
				authors.score[j] = new_score[j];
			}
		}
		System.out.println("Reach maximal iteration limitation.");
	}

	public static void test_score() {
		double base;

		score = new double[node_count];
		base = 0.0;
		for (int i = 0; i < node_count; i++) {
			score[i] = 0.0;
			if (outdegree[i] > 0) {
				if (outdegree[i] > base) {
					base = (double) outdegree[i];
				}
			}
		}

		base = Math.log(base + 1.0);
		for (int i = 0; i < node_count; i++) {
			score[i] = Math.log(outdegree[i] + 1);
			score[i] = score[i] / base;
		}
	}

	/*
	 * the score = link score + author score
	 */
	public static void output() {
		String path = OUT_PATH + "/static_score.txt";
		try {
			FileWriter fstream = new FileWriter(path);
			BufferedWriter out = new BufferedWriter(fstream);
			for (int i = 0; i < node_count; i++) {
				out.write(Double.toString(score[i]) + "\n");
			}
			out.flush();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public static void author_score_output() {
		String path = OUT_PATH + "/author_score.txt";
		Iterator<Integer> it = dtoa.iterator();
		int id;
		
		try {
			FileWriter fstream = new FileWriter(path);
			BufferedWriter out = new BufferedWriter(fstream);
			
			for (int i = 0; i < node_count; i++) {
				id = (Integer)it.next();
				if (id == -1){
					out.write("0\n");
				}else{
					out.write(Double.toString(authors.score[id]) + "\n");
				}
			}
			
			out.flush();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	/*
	 * load the configure file
	 */
	public static void initialize(String path) {
		BufferedReader br;
		String line;
		int i, j;
		
		try{
			//import the configure file
			br = new BufferedReader(new FileReader(new File(path)));
			while ((line = br.readLine()) != null){
				i = line.indexOf("\"");
				j = line.lastIndexOf("\"");
				if (line.contains("DB_PATH")){
					DB_PATH = line.substring(i+1, j);
				} else if (line.contains("DIC_PATH")){
					DIC_PATH = line.substring(i+1, j);
				}else if (line.contains("OUT_PATH")){
					OUT_PATH = line.substring(i+1, j);
				}
			}
			
			graphDb = new EmbeddedGraphDatabase(DB_PATH);
			docs = new HashMap<String, DocInfo>();
			authors = new AuthorGraph();
			dtoa = new LinkedList<Integer>(); 
		} catch (Exception e){
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		initialize(args[0]);
		System.out.println("reading files...");
		import_dict();
		System.out.println("total nodes: " + node_count);
		System.out.println("total author: " + authors.count);

		System.out.println("creating graph...");
		creat_graph();
		System.out.println("total relationships: " + rel_count);
		System.out.println("total author relationships: " + authors.rel_count);

		System.out.println("evaluting page rank score...");
		pagerank();
		author_score();

		System.out.println("output...");
		//author_score_output();
		output();

		System.out.println("application exits");
	}
}
