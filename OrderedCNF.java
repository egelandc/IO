import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.ThreadLocalRandom;


/** 
 * Class for storing a CNF formula with an associated ordering of its clauses
 * and literals. This order can be interpreted as a linear branch decomposition
 */
public class OrderedCNF {
    int variables; // number of variables
    int clauses;   // number of clauses
    private static int max_k = 17;
    private static int GreedyleftShiftingRounds = 7;
    private static int BaryleftShiftingRounds = 7;
    private boolean[] isNonEmpty; // whether a clause is empty or not
    
    
    /** 
     * The order. A positive integer x at position i means element i in order
     * is the clause numbered x, a negative integer means variable numbered x.
     */ 
    public int[] order;
    int [] cOrder;
    int [] vOrder; 
    public int[] clauseOrderPosition; //Gives the ordering of all clauses
    public int[] varOrderPosition; //Gives the ordering of all variables
    public int[] clauseOrder; //Gives the ordering of all clauses
    public int[] clausePositionInTotalOrdering; //keeps track of where clauses are positioned
    public int[] varPositionInTotalOrdering; //keeps track of where variables are positioned
    public int[] varOrder; //Gives the ordering of all variables
    public int[][] kClause;
    BitSet[] literals;
    BitSet[] clausesAtCut; // clauses on 'left side' of the index pos
    final static String ORDER_STRING = "c ORDER: ";
    final static String ORDER_VAR_STRING = "c_var ORDER: ";
    final static String ORDER_CLA_STRING = "c_cla ORDER: ";
    static void shuffleArray(int[] ar)
    {
      // If running on Java 6 or older, use `new Random()` on RHS here
      Random rnd = ThreadLocalRandom.current();
      for (int i = ar.length - 1; i > 0; i--)
      {
        int index = rnd.nextInt(i + 1);
        // Simple swap
        int a = ar[index];
        ar[index] = ar[i];
        ar[i] = a;
      }
    }

    /** 
     * Constructs a new formula based on instance description read from stdin.
     * If the boolean <code>orderGiven</code> is set, the order is assumed to
     * be supplied with the instance in the comments 
     * (on the form "c ORDER: v12 c21 v52 v32 c12 ..... "). 
     * If <code>orderGiven</code> is false, the order will be computed by a
     * greedy heuristic. 
     */
    static OrderedCNF readCNF (ORDERING ordering,int rounds) { // read from stdin
        Scanner sc = new Scanner( System.in );
        boolean headerFound = false;
        ArrayList<ArrayList<Integer>> varGraph;
        ArrayList<ArrayList<Integer>> claGraph;
        String stringOrder = null;
        String stringVarOrder = null;
        String stringClaOrder = null;
        String s = null;
        OrderedCNF cnf;
        int numVars = 0;
        int numClauses = 0;

        // in case the order is given (as a line in the comments)
        while (ordering.equals(ORDERING.SINGLE) && stringOrder == null) {
            String line = sc.nextLine();
            
            if (line.length() > ORDER_STRING.length()) {
                s = line.substring(0, ORDER_STRING.length());
                if (s.equals(ORDER_STRING)) {
                    stringOrder = line;
                }
            }
        }
        
        // in case the order is given by two linear orders
        while (ordering.equals(ORDERING.DOUBLE) && (stringVarOrder == null
        		|| stringClaOrder == null)) {
            String line = sc.nextLine();
            // variable ordering
            if (line.length() > ORDER_VAR_STRING.length()) {
                s = line.substring(0, ORDER_VAR_STRING.length());
                if (s.equals(ORDER_VAR_STRING)) {
                	stringVarOrder = line;
                }
            }
            // clause ordering
            if (line.length() > ORDER_CLA_STRING.length()) {
                s = line.substring(0, ORDER_CLA_STRING.length());
                if (s.equals(ORDER_CLA_STRING)) {
                	stringClaOrder = line;
                }
            }
        }
        
        // in case the order is given by two linear orders
        while (ordering.equals(ORDERING.DOUBLEK) && (stringVarOrder == null
        		|| stringClaOrder == null)) {
            String line = sc.nextLine();
            // variable ordering
            if (line.length() > ORDER_VAR_STRING.length()) {
                s = line.substring(0, ORDER_VAR_STRING.length());
                if (s.equals(ORDER_VAR_STRING)) {
                	stringVarOrder = line;
                }
            }
            // clause ordering
            if (line.length() > ORDER_CLA_STRING.length()) {
                s = line.substring(0, ORDER_CLA_STRING.length());
                if (s.equals(ORDER_CLA_STRING)) {
                	stringClaOrder = line;
                }
            }
        }
      
        // disregarding all lines until "p ...." is read
        while (!headerFound) {
            String line = sc.nextLine();

            if ( line.length() >= 1 && line.charAt(0) == 'p') {
                 headerFound = true;
                 String[] args = line.split(" ");
                 numVars = Integer.parseInt(args[2]);
                 numClauses = Integer.parseInt(args[3]);
            }
        } 
        
        cnf = new OrderedCNF(numVars, numClauses);
        varGraph = new ArrayList<ArrayList<Integer>>();
        claGraph = new ArrayList<ArrayList<Integer>>();
        
        //Add lists to hold clauses for each variable.
        for(int i = 0; i<numVars +1;i++){
        	varGraph.add(new ArrayList<Integer>());
        }
        
      //Add lists to hold variables for each clause.
        for(int i = 0; i<numClauses +1; i++){
        	claGraph.add(new ArrayList<Integer>());
        }
 
        /**
         * Timestamping - CEG
         */
        long start = System.nanoTime();
        
        boolean orderGiven = true;
        if(ordering.equals(ORDERING.K)){
			orderGiven = false;
			stringVarOrder = ORDER_VAR_STRING;
			stringClaOrder = ORDER_CLA_STRING;
        }
        BitSet inOrder = new BitSet(cnf.variables + 1);
        // Reading in the clauses
        for (int clause = 1; clause <= cnf.clauses; clause++) {
            String line = sc.nextLine();
            if(!orderGiven){
            	stringClaOrder += " c" + clause;
            }
            for (String token : line.split(" ")) {
                int value = Integer.parseInt(token);
                if (value == 0) break;
                boolean sign = (value > 0);
                if (!sign) value = -value;
                
                //If order is not given, build an ordering based on input.
                if(!orderGiven){
	                //Just build variable ordering from input.
	                if(!inOrder.get(value)){
	                	inOrder.set(value); //Variable is processed.
	                	stringVarOrder += " v" + value;
	                }  
                }
                cnf.put(clause, value, sign);
                //May hit multiple values, unless formula is preprocessed. //TODO: REVIEW THIS
                if(varGraph.get(Math.abs(value)) != null){
                
                }
                //Update graphs. 
                varGraph.get(Math.abs(value)).add(clause);
                claGraph.get(clause).add(Math.abs(value));
            }
        }
        
        //Duration in milliseconds.
        long duration = (long) ((System.nanoTime() - start)/Math.pow(10,6));
        double durationInSec = duration/(double)1000;
        //System.out.println("Reading Clauses - Running time: " + durationInSec + " seconds.");
        
        //System.out.println("Generating order");
        // Generating/finding an order

        switch(ordering){
	        case SINGLE:
	        	cnf.extractOrder(stringOrder);
	        	stringVarOrder = ORDER_VAR_STRING;
				stringClaOrder = ORDER_CLA_STRING;
				
				for(int i = 1 ; i < cnf.order.length ; i++){
					if(cnf.order[i] < 0){
						stringVarOrder += " v"+ Math.abs(cnf.order[i]);
					}
					else{
						stringClaOrder+= " c" + cnf.order[i];
					}
					
				}
				// Find position for clauses in the total ordering.
				for(int i = 1 ;i<cnf.order.length ; i++){
					if(cnf.order[i] > 0){
						cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
					}
					else{
						cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
					}
				}
				
				
	        	cnf.extractClauseOrder(stringClaOrder);
	        	cnf.extractVarOrder(stringVarOrder);
	        	
	        	cnf.countK(varGraph, claGraph,true);
	        	
	        
	        	System.out.println();
	        	break;
	        case NONE:
	        	//Testing out hybrid k-interval and greedy.
	            start = System.nanoTime();
	        	cnf.greedyOrder();
				
	        	stringVarOrder = ORDER_VAR_STRING;
				stringClaOrder = ORDER_CLA_STRING;
				
				for(int i = 1 ; i < cnf.order.length ; i++){
					if(cnf.order[i] < 0){
						stringVarOrder += " v"+ Math.abs(cnf.order[i]);
					}
					else{
						stringClaOrder+= " c" + cnf.order[i];
					}
					
				}
				// Find position for clauses and variables in the total ordering.
				for(int i = 1 ;i<cnf.order.length ; i++){
					if(cnf.order[i] > 0){
						cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
					}
					else{
						cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
					}
				}
				
				
	        	cnf.extractClauseOrder(stringClaOrder);
	        	cnf.extractVarOrder(stringVarOrder);
	        	
	        	
	        	//System.out.println(" Greedy: ");
	        	//cnf.kMergeOrderExt(varGraph, claGraph, false);
	        	//int totalK = cnf.countK(varGraph, claGraph,true);
	        	cnf.kMergeOrderExt(varGraph, claGraph, false);

				// Find position for clauses and variables in the total ordering.
				for(int i = 1 ;i<cnf.order.length ; i++){
					if(cnf.order[i] > 0){
						cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
					}
					else{
						cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
					}
				}
				
	        	int totalK = cnf.countK(varGraph, claGraph,true);
	        	

				int lShiftrounds1 = GreedyleftShiftingRounds;
	            while(lShiftrounds1-- > 0){
	            
		        	//Shift all clauses to the left
		        	if(true){
						for(int i = 1 ;i<cnf.order.length ; i++){
							if(cnf.order[i] > 0){
								cnf.order = cnf.shiftClause(cnf.order,i);
							}
						}
		        	}
		        	
		        	
		        	stringVarOrder = ORDER_VAR_STRING;
					stringClaOrder = ORDER_CLA_STRING;
					
					for(int i = 1 ; i < cnf.order.length ; i++){
						if(cnf.order[i] < 0){
							stringVarOrder += " v"+ Math.abs(cnf.order[i]);
						}
						else{
							stringClaOrder+= " c" + cnf.order[i];
						}
						
					}
					// Find position for clauses and variables in the total ordering.
					for(int i = 1 ;i<cnf.order.length ; i++){
						if(cnf.order[i] > 0){
							cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
						}
						else{
							cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
						}
					}
					
		        	cnf.extractClauseOrder(stringClaOrder);
		        	cnf.extractVarOrder(stringVarOrder);
		        	
					//cnf.countK(varGraph, claGraph,true);

		        	if(lShiftrounds1 == 0){
		        		cnf.countK(varGraph, claGraph,true);
		        	}
		        	else{
		        		 cnf.countK(varGraph, claGraph,false);
		        	}
					
	            }

	            //Duration in milliseconds.
	            duration = (long) ((System.nanoTime() - start)/Math.pow(10,6));
	            durationInSec = duration/(double)1000;
	            //System.out.println("Greedy running time: " + durationInSec + " seconds.");
	           System.exit(0);
	            if(totalK > 3000){
	            	//System.exit(0);
	            }
	            System.out.println(" total k : " + totalK);
	        	break;
	        case DOUBLE:
	        	//Merge Order if there exist an interval ordering.
	        	cnf.extractClauseOrder(stringClaOrder);
	        	cnf.extractVarOrder(stringVarOrder);
	        	cnf.mergeOrder(varGraph);
	        	break;
	        case DOUBLEK:
	        	//Merge Order if there exist an interval ordering.
	        	cnf.extractClauseOrder(stringClaOrder);
	        	cnf.extractVarOrder(stringVarOrder);
	        	cnf.kMergeOrder(varGraph, claGraph, true);
	        	break;
	        case K:
	        	boolean shiftcla= true;
	        	//Merge Order if there exist an interval ordering.
	        	cnf.extractClauseOrder(stringClaOrder);
	        	cnf.extractVarOrder(stringVarOrder);
	        	cnf.updatePositions();
				// Find position for clauses and variables in the total ordering.

	        	cnf.kMergeOrderExt(varGraph, claGraph, false);
				for(int i = 1 ;i<cnf.order.length ; i++){
					if(cnf.order[i] > 0){
						cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
					}
					else{
						cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
					}
				}
	        	totalK = cnf.countK(varGraph, claGraph,true);
	        	System.out.println("#variables = " + cnf.variables + " #clauses = " + cnf.clauses  );
	        	
	        	//Reading clauses linearly can cause a bias.
	        	//Shuffle arrays randomly so we get a better feel of heurstics
	        	//shuffleArray(cnf.clauseOrder);
	        	//shuffleArray(cnf.varOrder);
	        	//cnf.updatePositions();


	        	//Heuristics alternating between clause and variable orderings.
	        	start = System.nanoTime();
	        	for(int r = 1;r<=rounds;r++){
	        		//System.out.print(r + ", ");
	        		if (r%2 == 0){
	    	        	cnf.barycentre(false, varGraph);

	        		}
	        		else{
	    	        	cnf.barycentre(true, claGraph);
	        		}
	        		cnf.updatePositions();
	        	}
	        	cnf.updatePositions();
	            duration = (long) ((System.nanoTime() - start)/Math.pow(10,6));
	            durationInSec = duration/(double)1000;
	            //System.out.println("BaryCenter: " + durationInSec + " seconds.");

	            /**
	             * Timestamping - CEG
	             */
	            start = System.nanoTime();
	           //System.out.println(" Barycenter: ");
	            
	            //Merge linear orders, finding lowest k.
	            cnf.kMergeOrderExt(varGraph, claGraph, false);
	            
	            /**
	             * The stuff below is to optimize the linear ordering after
	             * k-merging.
	             */
	            
				// Find position for clauses and variables in the total ordering.
				for(int i = 1 ;i<cnf.order.length ; i++){
					if(cnf.order[i] > 0){
						cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
					}
					else{
						cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
					}
				}
				
				
				totalK = cnf.countK(varGraph, claGraph,true);
				 
	            int lShiftrounds2 = BaryleftShiftingRounds;
	            while(lShiftrounds2-- > 0){
	            
		        	//Shift all clauses to the left
		        	if(shiftcla){
						for(int i = 1 ;i<cnf.order.length ; i++){
							if(cnf.order[i] > 0){
								cnf.order = cnf.shiftClause(cnf.order,i);
							}
						}
		        	}
		        	
		        	stringVarOrder = ORDER_VAR_STRING;
					stringClaOrder = ORDER_CLA_STRING;
					
					for(int i = 1 ; i < cnf.order.length ; i++){
						if(cnf.order[i] < 0){
							stringVarOrder += " v"+ Math.abs(cnf.order[i]);
						}
						else{
							stringClaOrder+= " c" + cnf.order[i];
						}
						
					}
					// Find position for clauses and variables in the total ordering.
					for(int i = 1 ;i<cnf.order.length ; i++){
						if(cnf.order[i] > 0){
							cnf.clausePositionInTotalOrdering[cnf.order[i]] = i;
						}
						else{
							cnf.varPositionInTotalOrdering[Math.abs(cnf.order[i])] = i;
						}
					}
					
		        	cnf.extractClauseOrder(stringClaOrder);
		        	cnf.extractVarOrder(stringVarOrder);
		        	
		        	int temp;
		        	if(lShiftrounds2 == 0){
		        		temp = cnf.countK(varGraph, claGraph,true);
		        	}
		        	else{
		        		temp = cnf.countK(varGraph, claGraph,false);
		        	}
		        	if(temp < totalK) totalK = temp;
	            }
	            System.out.println(" total k : " + totalK);
	            //Duration in milliseconds.
	            duration = (long) ((System.nanoTime() - start)/Math.pow(10,6));
	            durationInSec = duration/(double)1000;
	            //System.out.println("K Merging running time: " + durationInSec + " seconds.");
	            System.exit(0);
	        	break;
        }
        
        cnf.applyOrder();
         
        return cnf;
    }
    
    /**
     * 
     * @param order Total ordering on variables and clauses
     * @param clausePosition Position of the clause to be shifted
     * @return
     */
    public int[] shiftClause(int[] order,int clausePosition){
    	
    	int l_length = kClause[order[clausePosition]][0];
    	int r_length = kClause[order[clausePosition]][1];
    	int length;
    	if (l_length > r_length){
    		length = (l_length - r_length) /2;
    	}
    	else{
    		return order;
    	}
    	
    	for(int i = 0; i < length;){
    		if(clausePosition > 1){
    			//Get element to the immediate left in the ordering
    			int temp = order[clausePosition -1]; 
    			if(temp < 0){
    				i++;
    			}

    			else{
    				//break;
    			}
    			order[clausePosition -1] = order[clausePosition] ;
    			order[clausePosition] = temp;
    			clausePosition--;
    		}
    		else{
    			break;
    		}
    	}
    	
    	return order;
    }
    
    public int[] shiftClauseRight(int[] order,int clausePosition){
    	
    	int l_length = kClause[order[clausePosition]][0];
    	int r_length = kClause[order[clausePosition]][1];
    	int length;
    	if (l_length < r_length){
    		length = (r_length - l_length) /2;
    	}
    	else{
    		return order;
    	}
    	
    	for(int i = 0; i < length;){
    		if(clausePosition < clauses + variables){
    			//Get element to the immediate left in the ordering
    			int temp = order[clausePosition +1]; 
    			if(temp < 0){
    				i++;
    			}
    			order[clausePosition +1] = order[clausePosition] ;
    			order[clausePosition] = temp;
    			clausePosition++;
    		}
    		else{
    			break;
    		}
    	}
    	
    	return order;
    }
    
    /**
     * 
     * @param order Total ordering on variables and clauses
     * @param clausePosition Position of the clause to be shifted
     * @return
     */
    public int[] shiftClauseToNewPosition(int[] order,int clausePosition,int newPos){
    	
    	//Move to the left or right
    	if(clausePosition > newPos){
    		int length = clausePosition - newPos;
	    	for(int i = 0; i < length;i++){
	    		if(clausePosition > 1){
	    			//Get element to the immediate left in the ordering
	    			int temp = order[clausePosition -1]; 
        			if(temp < 0){
        				varPositionInTotalOrdering[-temp]+=1;
        			}
	    			order[clausePosition -1] = order[clausePosition] ;
	    			order[clausePosition] = temp;
	    			clausePosition--;
	    			
	    		}
	    		else{
	    			break;
	    		}
	    	}
    	}
    	else{
    		int length = newPos - clausePosition;
        	for(int i = 0; i < length;i++){
        		if(clausePosition < clauses + variables){
        			//Get element to the immediate left in the ordering
        			int temp = order[clausePosition +1]; 
        			
        			if(temp < 0){
        				varPositionInTotalOrdering[-temp]-=1;
        			}
        			
        			order[clausePosition +1] = order[clausePosition] ;
        			order[clausePosition] = temp;
        			clausePosition++;
        		}
        		else{
        			break;
        		}
        	}
    	}
    	
    	return order;
    }
    
    /** 
     * Constructs a new OrderedCNF instance with given number of variables and
     * clauses. Order is NOT set and will cause error if not assigned and
     * applied 
     */
    public OrderedCNF(int variables, int clauses) {
        this.variables = variables;
        this.clauses = clauses;
        this.kClause = new int[clauses+1][2];
        this.literals = new BitSet[(variables+1)*2];            
        this.order = new int[clauses+variables+1];
        this.clauseOrderPosition = new int[clauses+1];
        
        this.clausePositionInTotalOrdering = new int[clauses+1];
        this.varPositionInTotalOrdering = new int[variables+1];
        this.varOrderPosition = new int[variables+1];
        this.clauseOrder = new int[clauses+1];
        this.varOrder = new int[variables+1];
        this.cOrder = new int[clauses+1];
        this.vOrder = new int[variables+1];
        this.isNonEmpty = new boolean[clauses+1]; 

        for (int i = 0; i < literals.length; i++) {
            literals[i] = new BitSet(clauses+1);
        }
    }

    /** 
     * Returns the number of empty clauses in this formula 
     */
    public int emptyClauseCount() {
        int num = 0;
        for (int i = 1; i < isNonEmpty.length; i++) {
            if(!isNonEmpty[i]) num++;
        }
        return num;
    }

    /** 
     * Generates the table <code>clausesAtCut</code> based on the current ordering 
     */
    public void applyOrder() {
        this.clausesAtCut = new BitSet[order.length];

        clausesAtCut[0] = new BitSet(clauses+1);
        for (int i = 1; i < order.length; i++) {
            clausesAtCut[i] = (BitSet) clausesAtCut[i-1].clone();
            if (order[i] > 0) // index i is a clause
                clausesAtCut[i].set(order[i]);
        }
    }

    /**
     * Extracts order from line of the form "c ORDER:  v1 c18 c2 cv4 ... " 
     */ 
    private void extractOrder(String s) {
        String[] tokens = s.split(" ");
        int orderInd = 1;
        for (int i = 1; orderInd <= clauses+variables; i++) {
            String token = tokens[i];
            if (token.length() < 1) continue;
            if (token.charAt(0) == 'c') { // a clause is read
                order[orderInd++] = Integer.parseInt(token.substring(1));
            } else if (token.charAt(0) == 'v'){ // a variable is read
                order[orderInd++] = -Integer.parseInt(token.substring(1));
            }
        } 
    }
    
    /**
     * Extracts order from line of the form "c cla ORDER: c18 c23 c9 ... " 
     */ 
    private void extractClauseOrder(String s) {
    	//Store positions of clauses
    	String[] tokens = s.split(" ");
    	int orderInd = 1;
    	for (int i = 1; orderInd <= clauses; i++) {
            String token = tokens[i];
            if (token.length() < 1) continue;
            if (token.charAt(0) == 'c') {
            	clauseOrder[orderInd] = Integer.parseInt(token.substring(1));
            	clauseOrderPosition[Integer.parseInt(token.substring(1))] = orderInd++;
            }
        }
    }
    
    /**
     * Extracts order from line of the form "c var ORDER: v18 v23 v9 ... " 
     */ 
    private void extractVarOrder(String s) {
    	//Store positions of variables
    	String[] tokens = s.split(" ");
    	if(tokens.length < variables){
    		System.out.println("Too few variables.");
    		System.exit(0);
    	}
    	int orderInd = 1;
    	for (int i = 1; orderInd <= variables; i++) {
            String token = tokens[i];
            if (token.length() < 1) continue;
            if (token.charAt(0) == 'v') {
            	varOrder[orderInd] = Integer.parseInt(token.substring(1));
            	varOrderPosition[Integer.parseInt(token.substring(1))] = orderInd++;
            }    
    	}
    }
    
    /**
     * Extracts order from line of the form "c var ORDER: v18 v23 v9 ... " 
     */ 
    private void updatePositions() {
    	//Store positions of variables

    	for(int i = 1; i < varOrder.length;i++){
    		varOrderPosition[varOrder[i]] = i;
    	}
    	
    	
    	for(int i = 1; i < clauseOrder.length;i++){
    		clauseOrderPosition[clauseOrder[i]] = i;
    	}
    }

    /**
     * Puts the described literal (variable 'var' either positive or negative,
     * depending on 'sign') into the given clause 'clause' 
     */
    public void put(int clause, int var, boolean sign) {
        int literal = (sign ? 2*var : 2*var + 1);
        literals[literal].set(clause);
        isNonEmpty[clause] = true;
    }

        
    /**
     * Writes this cnf-instance to standard output, with its order written in the
     * comments on the form "c ORDER:  c42 c21 v42 v13 c12 ..." if the 'printOrder'
     * boolean is set to true
     */
    public void output(boolean printOrder) {
        if (printOrder) {
            StringBuilder sb = new StringBuilder(order.length*10);
            StringBuilder sbVar = new StringBuilder(order.length*10);
            StringBuilder sbCla = new StringBuilder(order.length*10);
            
            for (int pos = 1; pos < order.length; pos++) {
                if (order[pos] > 0){
                	sb.append(" c" + order[pos]);
                	sbCla.append(" c" + order[pos]);
                }
                else{
                	sb.append(" v" + (-order[pos]));
                	sbVar.append(" v" + (-order[pos]));
                }
            }

            System.out.println("c ----------------");  
            System.out.println(ORDER_STRING + sb);
            //System.out.println(ORDER_CLA_STRING + sbCla);
            //System.out.println(ORDER_VAR_STRING + sbVar);
            System.out.println("c ----------------"); 
        }
        System.out.println("p cnf " + variables + " " + clauses);
        for (int clause = 1; clause <= clauses; clause++) {
            StringBuilder sb = new StringBuilder("");
            for (int var = 1; var <= variables; var++) {
                if (literals[2*var].get(clause))
                    sb.append(var + " ");
                else if (literals[2*var+1].get(clause))
                    sb.append("-" + var + " ");
            }
            System.out.println(sb + "0");
        }
        
    };

    /** 
     * A greedy heuristic for finding an ordering of the variables and 
     * clauses. It selects elements (variables and clauses) greedily in 
     * such a way that for element e_i at position i, no element e_j at a position j >
     * i is connected to more elements positioned before e_i than e_i itself, and
     * if they are connected to the same number of elements before e_i, then
     * e_i is connected to at most as many elements in total as e_j 
     */
    private void greedyOrder(){
        Element[] greedyOrder = new Element[clauses + variables + 1];
        Element[] clauseElements = new Element[clauses + 1];

        // Initializing
        for (int i = 1; i <= clauses; i++) {
            clauseElements[i] = new Element();
            clauseElements[i].representation = i; // representation of clause
            greedyOrder[i] = clauseElements[i];
        } 

        for (int i = 1; i <= variables; i++) {
            Element e = new Element();
            e.representation = -i;  // representation of variable
            greedyOrder[clauses + i] = e;
            for (int lit = i*2; lit <= i*2+1; lit++ ) {
                BitSet bs = literals[lit];
                int c = bs.nextSetBit(0);
                
                while (c >= 0) {
                    
                    Element cla = clauseElements[c];
                    cla.degree ++;
                    e.degree ++;
                    cla.adjacentTo.add(e);
                    e.adjacentTo.add(cla);
                    c = bs.nextSetBit(c+1); // finding next clause containing lit
               } 
            }
        }

        // Rearranging order greedily
        for (int i = 1; i < order.length; i++) {
        
            int best = i;
            
            for (int j = i; j < order.length; j++) {
                if (greedyOrder[j].compareTo(greedyOrder[best]) < 0) {
                    best = j;
                }
            }
         
            for (Element adj: greedyOrder[best].adjacentTo) {
                adj.LDegree++; // neighbours of element chosen in order
                               // position i now have 1 higher LDegree 
            }
            
            /* updating the order according to choice made by greedy heuristic,
               and updating greedyOrder so that all unchosen elements are in 
               position i+1 or higher. */
            order[i] = greedyOrder[best].representation; 
            greedyOrder[best] = greedyOrder[i]; 
        }
    }

    /** Class used for GreedyOrder-method */
    private class Element{
        int representation = 0;
        int LDegree = 0;
        int degree = 0;
        ArrayList<Element> adjacentTo = new ArrayList<Element>();
        
        int compareTo(Element e){
            if (LDegree == e.LDegree) {
                return degree - e.degree;
            } else return e.LDegree - LDegree;
        }
    }
    
    //TODO Implement verifier
    //TODO Simple preprocessing, removing clauses with a variable occuring neg
    // and pos
    /** 
     * Algorithm for merging two linear orders of variables and clauses
     * into an interval ordering. It selects elements (variables and clauses) greedily in 
     */
    private void mergeOrder(ArrayList<ArrayList<Integer>> graph){
    	//Build ordering
    	int adjecentClauseCount = 0;
    	BitSet adjecentClauses = new BitSet(clauses +1);
    	int orderInd = 1;
    	int currentClause = 1;
    	
    	//Place all variables in the ordering.
    	for (int i = 1; i <= variables; i++) {
    		//Next variable to merge
    		int var = varOrderPosition[i];
    		int matched = 0;
    		
    		if(adjecentClauseCount > 0){
    			//Count adjecent clauses
    			for(Integer j : graph.get(var)){
    				if(adjecentClauses.get(j)){
    					matched++;
    				}
    			}
    			
    			//Skip clauses until we find legal position for var.
    			while(matched != adjecentClauseCount){
    				int clause = clauseOrderPosition[currentClause++];
    				order[orderInd++] = clause;
    				//TODO FIX MATCHED ERROR? Probably fixed
    				if(adjecentClauses.get(clause)){
    					adjecentClauseCount--;
    					adjecentClauses.clear(clause);
    					//Check if we skip adjecent clause
    					if(literals[2*var].get(clause) || literals[2*var +1].get(clause)){
    						matched--;
    					}
    				}
    			}
    			
    			//Add variable to the order and adjecent clauses
    			order[orderInd++] = -var;
    			for(Integer j : graph.get(var)){
    				if(!adjecentClauses.get(j) && (clauseOrderPosition[j] >= currentClause)){
    					adjecentClauseCount++;
    					adjecentClauses.set(j);
    				}
    			}
    		}
    		else{
    			//Add variable to the order
    			order[orderInd++] = -var;
    			//Add adjecent clauses
    			for(Integer j : graph.get(var)){
    				if(clauseOrderPosition[j] >= currentClause)
    				{
    					adjecentClauseCount++;
    					adjecentClauses.set(j);
    				}
    			}
    		}
    	}
    	
    	//Add rest of clauses
    	for (int i = currentClause; i <= clauses; i++) {
			order[orderInd++] = clauseOrderPosition[currentClause++];
    	}
    	
    	//Verify proper interval ordering.
    	for(int i = 1; i <= orderInd; i++){
    		
    	}
    }
    
    //Implement k interval merge ordering algorithm.
    //TODO Simple preprocessing, removing clauses with a variable occuring neg
    // and pos
    /** 
     * Algorithm for merging two linear orders of variables and clauses
     * into an interval ordering. It selects elements (variables and clauses) greedily in 
     */
    private void kMergeOrder(ArrayList<ArrayList<Integer>> varGraph, 
    		ArrayList<ArrayList<Integer>> claGraph, boolean givenClauseOrder){

    	int k = 0; //Starting value of k.
    	boolean success = false;
    	
    	//Loop until k value is found.
    	while(!success){
        	int[] varAdjCla = new int[variables+1]; //Array for holding adj. cla. lower than cut
        	int adjClaSize = 0; //Size of varAdjCla
        	int orderInd = variables + clauses; //Start with the highest position
        	int currentVarPos = variables + 1; //Positioned after last variable
        	boolean clauseFailed = false;
        	int clause;
	    	//Place all clauses in the ordering.
        	ClauseLoop:
	    	for (int i = clauses; i >= 1; i--) {
	    		//Next clause to merge
	    		clause = clauseOrder[i];

	    		int matched = 0;
	    		int lowestOrderedVarPos = -1;
	    		int lowVarCount = 0;
	    		//look at all adj. vars for clause. do stuff.
	    		for(int j = 0; j < claGraph.get(clause).size(); j++){
	    			int var = claGraph.get(clause).get(j); // Do not store this when done.
	    			if(adjClaSize > 0){
	    				if(varAdjCla[var] > 0){
	    					if(literals[2*var].get(clause) || literals[2*var +1].get(clause)){
	    						matched++;
	    					}
	    				}
	    			}
	    			
	    			//Keep track of vars positioned before current pos
	    			if(varOrderPosition[var] < currentVarPos){
	    				lowVarCount++;
	    				if(lowestOrderedVarPos == -1){
	    					lowestOrderedVarPos = varOrderPosition[var];
	    				}

	    				if(varOrderPosition[var] < lowestOrderedVarPos){
	    					lowestOrderedVarPos = varOrderPosition[var];
	    				}
	    			}
	    		}
	    		
	    		//Vars needed for clause in higher pos. than cut.
	    		int kRight = adjClaSize - matched;
	    		int kLeft = 0;
	    		if(lowestOrderedVarPos < currentVarPos && lowestOrderedVarPos > 0){
	    			kLeft = currentVarPos - lowestOrderedVarPos - lowVarCount;
	    		}
	    		
	    		//If we found possible position, continue with next clause.
	    		if((kRight + kLeft) <= k){
	    			order[orderInd--] = clause;
	    			
	    			//Remove vars req in kRight by the positioned clause.
	    			for (int v : claGraph.get(clause)){
	    				if(varOrderPosition[v] > currentVarPos){
	    					if (varAdjCla[v] > 1){
	    						varAdjCla[v]--;
	    					}
	    					else if (varAdjCla[v] == 1){
		    						adjClaSize--;
		    						varAdjCla[v]--;
	    					}
	    				}
	    			}
	    			System.out.println("kRight:" + kRight);
	    			System.out.println("kLeft:" + kLeft);
	    			//Next iteration
	    			continue ClauseLoop;
	    		}

	    		//Try moving the clause left to find a valid position.
	    		while(kRight <= k){
	    			//Add next variable to the order.
	    			int var = varOrder[--currentVarPos];
	    			order[orderInd--] = -var;
	    			
	    			//Update kRight
	    			for (int cla : varGraph.get(var)){
	    				if(clauseOrderPosition[cla] < clauseOrderPosition[clause]){
	    					//Only count new clauses.
	    					if(varAdjCla[var] == 0){
	    						adjClaSize++;
	    					}
	    					varAdjCla[var]++;
	    				}
	    			}
	    			
	    			//If skipped var is adjacent to clauses before this, we must add var to clause.
	    			if( varAdjCla[var] > 0  && !(literals[2*var].get(clause) || 
	    					literals[2*var +1].get(clause))){
	    				kRight++;
	    			}
	    			
	    			//Update left.
	    			if(!(literals[2*var].get(clause) || 
	    					literals[2*var +1].get(clause)) && kLeft > 0){
	    				kLeft--;
	    			}
	    			
		    		//If we found possible position, continue with next clause.
		    		if((kRight + kLeft) <= k){
		    			order[orderInd--] = clause;
		    			
		    			//Remove vars req in kRight by the positioned clause.
		    			for (int v : claGraph.get(clause)){
		    				if(varOrderPosition[v] > currentVarPos){
		    					if (varAdjCla[v] > 1){
		    						varAdjCla[v]--;
		    					}
		    					else if (varAdjCla[v] == 1){
			    						adjClaSize--;
			    						varAdjCla[v]--;
		    					}
		    				}
		    			}
		    			
		    			System.out.println("kRight:" + kRight);
		    			System.out.println("kLeft:" + kLeft);
		    			//Next iteration in outer loop.
		    			continue ClauseLoop;
		    		}
	    		}
	    		
	    		//No position found for current clause. Increase k.
	    		clauseFailed = true;
	    		break;
	    	}
	    	
	    	//Increment k value.
	    	if(clauseFailed){
	    		k++;
	    	}
	    	else{
	    		//Add rest of vars to the ordering... stuff stuff..
	    		success = true;
	    		while(currentVarPos > 0){
	    			order[orderInd--] = -varOrder[--currentVarPos];
	    		}
	    	}
	    	/*
	    	if(k>max_k){
	    		System.out.println("Aborting alg. to large k = " + k);
	    		System.exit(0);
	    	}*/
	    	
	    }
    	
	    	System.out.println(" k = " + k );
	    	System.out.println("Number of variables = " + variables  );
	    	if(k < (variables/10)){
    		System.out.println("------------------------------------------------------------");
    		System.out.println("------------------------------------------------------------");
    		System.out.println("------------------------------------------------------------");
    		System.out.println("------------------------------------------------------------");
    		System.out.println("------------------------------------------------------------");
    		System.out.println("------------------------------------------------------------");
    	}
	    
    }
    /**
     * Apply barycenter algorithm.
     * If lockVars = true, permute clauses. Else permute variables.
     */
    private void barycentre(boolean lockVars, ArrayList<ArrayList<Integer>> graph){
    	double[] newOrdering;
    	int[] newOrdering_pos;
    	//Set size of new ordering.
    	if(!lockVars){
    		newOrdering = new double[variables+1];
    		newOrdering_pos = new int[variables+1];
    		//position stuff
    		for(int i = 1; i <= variables;i++){
    			//Find all positions
    			int tot = 0;
    			
    			for(int j: graph.get(i)){
    				tot += clauseOrderPosition[j];
    			}
    			newOrdering_pos[i] = i;
    			newOrdering[i] = (double)tot/graph.get(i).size();
    		}
    	}
    	else{
    		//Do the opposite........
    		newOrdering = new double[clauses +1];
    		newOrdering_pos = new int[clauses +1];
    		//position stuff
    		for(int i = 1; i <= clauses;i++){
    			//Find all positions
    			int tot = 0;
    			
    			for(int j: graph.get(i)){
    				tot += varOrderPosition[j];
    			}
    			newOrdering_pos[i] = i;
    			newOrdering[i] = (double) tot/graph.get(i).size();
    		}
    	}
    

    	if(!lockVars){
    		//mergeSort(newOrdering,true);
    		quicksort(newOrdering, 1, variables, true,newOrdering_pos);
    		for(int i = 1; i <= variables;i++){
    			varOrder[i] = newOrdering_pos[i];
    		}
    	}
    	//Order clauses
    	else{
    		//mergeSort(newOrdering,false);
    		quicksort(newOrdering, 1, clauses, false,newOrdering_pos);
    		for(int i = 1; i <= clauses;i++){
    			clauseOrder[i] = newOrdering_pos[i];
    		}
    	}
    	
    }
    
    @SuppressWarnings("rawtypes")
	public void mergeSort(Comparable [ ] a,boolean orderVars)
	{
		Comparable[] tmp = new Comparable[a.length];
		int[] tmp2 = new int[a.length];
		mergeSort(a, tmp,  1,  a.length - 1, tmp2, orderVars);
	}


	@SuppressWarnings("rawtypes")
	private void mergeSort(Comparable [ ] a, Comparable [ ] tmp, int left, int right,int[] tmp2,boolean orderVars)
	{
		if( left < right )
		{
			int center = (left + right) / 2;
			mergeSort(a, tmp, left, center,tmp2,orderVars);
			mergeSort(a, tmp, center + 1, right,tmp2,orderVars);
			merge(a, tmp, left, center + 1, right,tmp2,orderVars);
		}
	}


    @SuppressWarnings({ "unchecked", "rawtypes" })
	private void merge(Comparable[ ] a, Comparable[ ] tmp, int left, int right, int rightEnd, int[] tmp2,boolean orderVars)
    {
        int leftEnd = right - 1;
        int k = left;
        int num = rightEnd - left + 1;

        while(left <= leftEnd && right <= rightEnd)
            if(a[left].compareTo(a[right]) <= 0){
            	tmp[k] = a[left];
            	
            	if(orderVars){
            		tmp2[k] = varOrder[left];
            	}
            	else{
            		tmp2[k] = clauseOrder[left];
            	}

            	k++; 
            	left++;
            }
                
            else{
            	tmp[k] = a[right];
            	if(orderVars){
            		tmp2[k] = varOrder[right];
            	}
            	else{
            		tmp2[k] = clauseOrder[right];
            	}
            	k++;
            	right++;
            }
                

        while(left <= leftEnd){    // Copy rest of first half
            tmp[k] = a[left];
        	if(orderVars){
        		tmp2[k] = varOrder[left];
        	}
        	else{
        		tmp2[k] = clauseOrder[left];
        	}
        	k++;
        	left++;
            
        }
        
        while(right <= rightEnd){  // Copy rest of right half
            tmp[k] = a[right];
        	if(orderVars){
        		tmp2[k] = varOrder[right];
        	}
        	else{
        		tmp2[k] = clauseOrder[right];
        	}
        	k++;
        	right++;
            
        }
        
        int temp = rightEnd;
        // Copy tmp back
        for(int i = 0; i < num; i++, rightEnd--)
            a[rightEnd] = tmp[rightEnd];
        
        rightEnd = temp;
        if(orderVars){
            for(int i = 0; i < num; i++, rightEnd--)
                varOrder[rightEnd] = tmp2[rightEnd];
        }
        else{
            for(int i = 0; i < num; i++, rightEnd--)
                clauseOrder[rightEnd] = tmp2[rightEnd];
        }
    }
    
    
    
    /**
     * 
     * @param dataToBeSorted Auxillirary data used to sort elements
     * @param left
     * @param right
     */
    public void quicksort(double[] dataToBeSorted,int left, int right,boolean orderVars,int[] newOrdering_pos){
    	int index = partition(dataToBeSorted, left, right,orderVars,newOrdering_pos);
    	if(left < index -1){
    		quicksort(dataToBeSorted,left, index -1,orderVars,newOrdering_pos);
    	}
    	if(index < right) {
    		quicksort(dataToBeSorted,index, right,orderVars,newOrdering_pos);
    	}
    }
    
    int partition (double[] arr, int left, int right, boolean orderVars,int[] newOrdering_pos){
    	double pivot = arr[(right + left)/2];
    	
    	while(left <= right){
    		//Find element on the left that should be on right
    		while(arr[left] < pivot) left++;
    		//Find element on right that should be on left
    		while(arr[right] > pivot) right--;
    		
    		//Swap elements, and move left and right indicies
    		if(left <= right){
                double tmp = arr[left];
                arr[left] = arr[right];
                arr[right] = tmp;
                
                int tmp2 = newOrdering_pos[left];
                newOrdering_pos[left] = newOrdering_pos[right];
                newOrdering_pos[right] = tmp2;

                left++;
                right--;

    		}
    	}
    	
    	return left;
    }
    
    /** 
     * Just move all clauses to its average position, i.e. avg. 
     * var pos in its total ordering
     * 
     */
    //TODO: Maybe change this? based on ordering in varorder? any reason?
    public void simpleMerge(ArrayList<ArrayList<Integer>> varGraph, 
    		ArrayList<ArrayList<Integer>> claGraph){
    	
		for(int i = 1 ;i<order.length ; i++){
			if(order[i] > 0){
				int clause = order[i];
				//calculate new position for order[i]
				int newPos = 0;
    			for(int j: claGraph.get(clause)){
    				newPos += varPositionInTotalOrdering[j];
    			}
    			newPos = newPos/claGraph.get(clause).size();
				
				order = shiftClauseToNewPosition(order,i,newPos);
			}
		}
		
		
    }
    
    /** 
     * Algorithm for merging two linear orders of variables and clauses
     * into an interval ordering. It selects elements (variables and clauses) greedily in 
     */
    public int countK(ArrayList<ArrayList<Integer>> varGraph, 
    		ArrayList<ArrayList<Integer>> claGraph,boolean print){
    	int totalKsum = 0;
    	int totalLeftSum = 0;
    	int totalRightSum = 0;
    	int maxK = 0;
    	//Find clause
    	for(int i = 1; i< order.length; i++){ 
    		
    		if(order[i] > 0){
    			int kLeft = 0, kRight = 0;
    			//Count k for clause order[i]
    			int clause = order[i];
    			int lowestOrderedVar = -1;
    			int lowVarCount = 0;
    			//Count partial left K
	    		for(int j = 0; j < claGraph.get(clause).size(); j++){
	    			int var = claGraph.get(clause).get(j); // Do not store this when done.

	    			//Keep track of vars positioned before current pos
	    			if(varPositionInTotalOrdering[var] < i){
	    				lowVarCount++;
	    				if(lowestOrderedVar == -1){
	    					lowestOrderedVar = var;
	    				}

	    				if(varPositionInTotalOrdering[var] < varPositionInTotalOrdering[lowestOrderedVar]){
	    					lowestOrderedVar = var;
	    				}
	    			}
	    		}
	    		
	    		if(lowVarCount > 0){
	    			for(int j = varPositionInTotalOrdering[lowestOrderedVar]; j< i;j++)
	    			{
	    				if(order[j] < 0){
	    					kLeft++;
	    				}
	    			}	
	    			kLeft = kLeft - lowVarCount;
	    		}
	    		
	    		//System.out.println("For clause : " + clause + " Kleft = " + kLeft );
	    	
    			//Count partial right K
	    		ClauseLoop:
	        	for(int j = i+1; j < order.length; j++){ 
	        		
	        		int kRightTemp = 0;
	        		if(order[j] < 0){
	        			
	        			int var = Math.abs(order[j]);
	        			
	        			//Check if clause contains var
	    	    		for(int k = 0; k < claGraph.get(clause).size(); k++){
	    	    			int tempvar = claGraph.get(clause).get(k); // Do not store this when done.
	    	    			if (var == tempvar ){
	    	    				continue ClauseLoop;
	    	    			}
	    	    		}
	        			
	        			//Count partial left K
	    	    		for(int k = 0; k < varGraph.get(var).size(); k++){
	    	    			int cla = varGraph.get(var).get(k); // Do not store this when done.
	    	    			
	    	    			if(clausePositionInTotalOrdering[cla] < i){
	    	    				kRightTemp++;
	    	    			}
	    	    		}
	        		}
	        		if(kRightTemp > 0){
	        			kRight++;
	        		}
	        		
	        	}
	    		
	        	if (( kRight + kLeft) > maxK ){
	        		maxK = kRight + kLeft;
	        	}
	    		//System.out.println("For clause : " + clause + " Kright= " + kRight);
	    		//System.out.println("For clause : " + clause + " SUM " + (kRight + kLeft));
	    		totalKsum += kRight + kLeft;
	    		totalLeftSum+=kLeft;
	    		totalRightSum+=kRight;
	    		kClause[clause][0] = kLeft;
	    		kClause[clause][1] = kRight;
    		}
    	}
    	
    	if(print){
        	//System.out.println("TOTAL SUM OF K : " + totalKsum + " . Total Left: " +totalLeftSum + " . Total Right " +totalRightSum);
        	System.out.println("Max_K : " + maxK);
    	}
    	
    	return totalKsum;
    }
    
    
    /** 
     * Algorithm for merging two linear orders of variables and clauses
     * into an interval ordering. It selects elements (variables and clauses) greedily in 
     */
    private void kMergeOrderExt(ArrayList<ArrayList<Integer>> varGraph, 
    		ArrayList<ArrayList<Integer>> claGraph, boolean givenClauseOrder){

    	int k = 0; //Starting value of k.
    	boolean success = false;
    	
    	//Loop until k value is found.
    	while(!success){
        	int[] varAdjCla = new int[variables+1]; //Array for holding adj. cla. lower than cut
        	int adjClaSize = 0; //Size of varAdjCla
        	int orderInd = variables + clauses; //Start with the highest position
        	int currentVarPos = variables + 1; //Positioned after last variable
        	boolean clauseFailed = false;
        	int clause;
	    	//Place all clauses in the ordering.
        	ClauseLoop:
	    	for (int i = clauses; i >= 1; i--) {
	    		//Next clause to merge
	    		clause = clauseOrder[i];

	    		int matched = 0;
	    		int lowestOrderedVarPos = -1;
	    		int lowVarCount = 0;
	    		//look at all adj. vars for clause. do stuff.
	    		for(int j = 0; j < claGraph.get(clause).size(); j++){
	    			int var = claGraph.get(clause).get(j); // Do not store this when done.
	    			if(adjClaSize > 0){
	    				if(varAdjCla[var] > 0){
	    					if(literals[2*var].get(clause) || literals[2*var +1].get(clause)){
	    						matched++;
	    					}
	    				}
	    			}
	    			
	    			//Keep track of vars positioned before current pos
	    			if(varOrderPosition[var] < currentVarPos){
	    				lowVarCount++;
	    				if(lowestOrderedVarPos == -1){
	    					lowestOrderedVarPos = varOrderPosition[var];
	    				}

	    				if(varOrderPosition[var] < lowestOrderedVarPos){
	    					lowestOrderedVarPos = varOrderPosition[var];
	    				}
	    			}
	    		}
	    		
	    		//Vars needed for clause in higher pos. than cut.
	    		int kRight = adjClaSize - matched;
	    		int kLeft = 0;
	    		if(lowestOrderedVarPos < currentVarPos && lowestOrderedVarPos > 0){
	    			kLeft = currentVarPos - lowestOrderedVarPos - lowVarCount;
	    		}
	    		
	    		//If we found possible position, continue with next clause.
	    		if((kRight + kLeft) <= k){
	    			order[orderInd--] = clause;
	    			//System.out.println("k for clause: " + clause + ": " + k);
	    			//Remove vars req in kRight by the positioned clause.
	    			for (int v : claGraph.get(clause)){
	    				if(varOrderPosition[v] > currentVarPos){
	    					if (varAdjCla[v] > 1){
	    						varAdjCla[v]--;
	    					}
	    					else if (varAdjCla[v] == 1){
		    						adjClaSize--;
		    						varAdjCla[v]--;
	    					}
	    				}
	    			}
	    			//System.out.println("kRight:" + kRight);
	    			kClause[clause][0] = kLeft;
	    			kClause[clause][1] = kRight;
	    			//System.out.println("kLeft:" + kLeft);
	    			//Next iteration
	    			continue ClauseLoop;
	    		}

	    		//Try moving the clause left to find a valid position.
	    		while(kRight <= k){
	    			//Add next variable to the order.
	    			int var = varOrder[--currentVarPos];
	    			order[orderInd--] = -var;
	    			
	    			//Update kRight
	    			for (int cla : varGraph.get(var)){
	    				if(clauseOrderPosition[cla] < clauseOrderPosition[clause]){
	    					//Only count new clauses.
	    					if(varAdjCla[var] == 0){
	    						adjClaSize++;
	    					}
	    					varAdjCla[var]++;
	    				}
	    			}
	    			
	    			//If skipped var is adjacent to clauses before this, we must add var to clause.
	    			if( varAdjCla[var] > 0  && !(literals[2*var].get(clause) || 
	    					literals[2*var +1].get(clause))){
	    				kRight++;
	    			}
	    			
	    			
	    			
	    			//Update left.
	    			if(!(literals[2*var].get(clause) || 
	    					literals[2*var +1].get(clause)) && kLeft > 0){
	    				kLeft--;
	    			}
	    			
		    		//If we found possible position, continue with next clause.
		    		if((kRight + kLeft) <= k){
		    			order[orderInd--] = clause;
		    			//System.out.println("k for clause: " + clause + ": " + k);
		    			//Remove vars req in kRight by the positioned clause.
		    			for (int v : claGraph.get(clause)){
		    				if(varOrderPosition[v] > currentVarPos){
		    					if (varAdjCla[v] > 1){
		    						varAdjCla[v]--;
		    					}
		    					else if (varAdjCla[v] == 1){
			    						adjClaSize--;
			    						varAdjCla[v]--;
		    					}
		    				}
		    			}
		    			kClause[clause][0] = kLeft;
		    			kClause[clause][1] = kRight;
		    			//System.out.println("kRight:" + kRight);
		    			//System.out.println("kLeft:" + kLeft);
		    			//Next iteration in outer loop.
		    			continue ClauseLoop;
		    		}
	    		}
	    		
	    		//No position found for current clause. Increase k.
	    		clauseFailed = true;
	    		break;
	    	}
	    	
	    	//Increment k value.
	    	if(clauseFailed){
	    		k++;
	    	}
	    	else{
	    		//Add rest of vars to the ordering... stuff stuff..
	    		success = true;
	    		while(currentVarPos > 0){
	    			order[orderInd--] = -varOrder[--currentVarPos];
	    		}
	    	}
	    }
    	//System.out.println("kClause SUM : " + countkClause());
    	System.out.println(" k = " + k );
    	//System.out.println("#variables = " + variables + "#clauses = " + clauses  );
    }
    
    /**
     * Calculate the total Right and Left k for every clause. 
     * @return sum of all k
     */
    int countkClause(){
    	int sum = 0;
    	
    	for(int i = 0; i < kClause.length;i++){
    		sum+=kClause[i][0] + kClause[i][1];
    	}
    	
    	return sum;
    }

}