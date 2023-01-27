// Hex Game + basic AI Bot opponent (using Monte Carlo's algorithm)
// Ángel Mateo Arenas
// January 2023

// =============================
// Some notes about the program:
// =============================

// ***************************************************************************************************
// - Some main classes in this project are Graph and its derived classes undirected_Graph and Hex_Board.
// - The class ShortestPath and its auxiliary class PriorityQueue are important for checking the win
// situation in the Hex game.
// - Hex_Game is the class that makes a game object. Such game object manages the game flow, makes the
// moves and checks if any player has won after each move. It contains the Hex board and all the
// required stuff. Now it also contains the implementation of the bot opponent using Monte Carlo simulation
// ---------------------------------------------------------------------------------------------------
// Some auxiliary classes are needed for certain operations and data managing. Those classes
// are PriorityQueue, bool_and_num_Pair, int_and_num_Pair and int_int_and_num_Triad.
// ---------------------------------------------------------------------------------------------------
// - The criterion for naming vertices and edges in our graphs is to name them from 0 to N_vertices-1
// and from 0 to N_edges-1.
// - Our Hex board is a graph which has a border length of L, so that the size of that graph is L*L.

#include <string> // Neccesary for using std::to_string(int)
#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
#include <fstream>
#include <iterator>
#include <stdio.h> // (In some cases, old C printf() will be used to print formatted text)
#include <typeinfo>
#include <utility>
using namespace std;

typedef enum representationMode{CON_MATRIX, EDGE_LIST} representationMode;

// The pseudorandom generator will be used as specified in https://en.cppreference.com/w/cpp/numeric/random/uniform_real_distribution
// This produces random floating-point values uniformly distributed on the interval [a,b)
std::mt19937 gen(time(0)); // Standard mersenne_twister_engine seeded time(0)
std::uniform_real_distribution<float> probability_having_edge(0.0, 1.0);
std::uniform_real_distribution<double> cost_value(0.0, 10.0);

std::uniform_real_distribution<double> probability_using_swap(0.0, 1.0); // Probability that is used in Monte Carlo Bot opponent

auto randengine = std::default_random_engine {}; // Needed for shuffling vectors using STL

int const N_MC_ITERATIONS = 750; // How many simulations for each movement in Monte Carlo bot opponent

namespace Graph{
    // ===============================================================================================
    // Auxiliary classes:
    // ===============================================================================================
    template<typename numType>
    class bool_and_num_Pair{ // An auxiliary class to store a pair of boolean and numerical values
        public:
            bool_and_num_Pair():_bool(false),_val(static_cast<numType>(0)){} // Default constructor
            bool_and_num_Pair(bool bvalue, numType val):_bool(bvalue),_val(val){}
            bool get_bool(){return _bool;}
            numType get_value(){return _val;}
            void set_bool(bool input){_bool=input; return;}
            void set_value(numType input){_val=input; return;}
            void set_pair(bool bool_value, numType num_value){_bool=bool_value; _val=num_value; return;}

        private:
            bool _bool;
            numType _val;
    };

    template<typename numType>
    class int_and_num_Pair{ // Another auxiliary class. This one is to store a pair of int and any-numerical-type values
        public:
            int_and_num_Pair():_val1(0),_val2(static_cast<numType>(0)){} // Default constructor
            int_and_num_Pair(int val1, numType val2):_val1(val1),_val2(val2){}
            int get_value1(){return _val1;}
            numType get_value2(){return _val2;}
            void set_value1(int val1){_val1=val1; return;}
            void set_value2(numType val2){_val2=val2; return;}
            void set_pair(int val1, numType val2){_val1=val1; _val2=val2; return;}

        private:
            int _val1;
            numType _val2;
    };

    template<typename numType>
    class int_int_and_num_Triad{ // Another auxiliary class. This one is to store a pair of ints and a numerical-type value
        public:
            int_int_and_num_Triad():_val1(0),_val2(0),_val3(static_cast<numType>(0)){} // Default constructor
            int_int_and_num_Triad(int val1, int val2, numType val3):_val1(val1),_val2(val2),_val3(val3){}
            int get_value1(){return _val1;}
            int get_value2(){return _val2;}
            numType get_value3(){return _val3;}
            void set_value1(int val1){_val1=val1; return;}
            void set_value2(int val2){_val2=val2; return;}
            void set_value3(numType val3){_val3=val3; return;}
            void set_triad(int val1, int val2, numType val3){_val1=val1; _val2=val2; _val3=val3; return;}

        private:
            int _val1;
            int _val2;
            numType _val3;
    };

    // ===============================================================================================
    // parent class Graph
    // ===============================================================================================
    template<typename numType>
    class Graph{

        protected:
            // Constructors:
            // =============
            Graph(int size, representationMode rep):size(size),preferredRepresentation(rep),\
            conMatrix_was_computed(false),edgeList_was_computed(false){}

            Graph(int size, representationMode rep, vector<numType> nodeValues):size(size),preferredRepresentation(rep),\
            nodeValues(nodeValues),conMatrix_was_computed(false),edgeList_was_computed(false){}

            // Copy constructor:
            Graph(const Graph<numType>& sample):size(sample.V()),connectivityMatrix(sample.private_getConMatrix()),\
            edgeList(sample.private_getEdgeList()),preferredRepresentation(sample.get_preferredRepresentation()),\
            nodeValues(sample.get_nodeValues()),nodeTags(sample.get_nodeTags()),\
            conMatrix_was_computed(sample.get_conMatrixWasComputed()),\
            edgeList_was_computed(sample.get_edgeListWasComputed()){}

        public:
            // Common methods for the derived classes:
            // =======================================
            ~Graph(){ // Destructor
                conMatrix_destruction();
                edgeList_destruction();
            }

            void conMatrix_destruction(){ // A submethod for destructing
                for(int i=0; i<connectivityMatrix.size(); ++i){
                    connectivityMatrix[i].clear();
                }
                connectivityMatrix.clear();
                return;
            }

            void edgeList_destruction(){ // A submethod for destructing
                for(int i=0; i<edgeList.size(); ++i){
                    edgeList[i].clear();
                }
                edgeList.clear();
                return;
            }

            void generate_conMatrix_from_edgeList(){
                if(edgeList_was_computed==true){
                    // Reset the matrix and initialize it to false. Then copy the info from the edge list
                    conMatrix_destruction();
                    for(int i=0; i<size; ++i){
                        connectivityMatrix.push_back(vector<bool_and_num_Pair<numType>>());
                        for(int j=0; j<size; ++j){
                            connectivityMatrix[i].push_back(bool_and_num_Pair(false, 0));
                        }
                    }
                    int auxIndex;
                    numType costAux;
                    for(int i=0; i<size; ++i){
                        for(int j=0; j<edgeList[i].size(); ++j){
                            auxIndex = edgeList[i][j].get_value1();
                            costAux = edgeList[i][j].get_value2();
                            connectivityMatrix[i][auxIndex] = bool_and_num_Pair(true, costAux);
                        }
                    }
                    conMatrix_was_computed = true;
                    return;
                }else{
                    cout<<"Edge list has not been generated yet, so connectivity matrix can't be generated from it!."
                    <<endl;
                    return;
                }
            }

            void generate_edgeList_from_conMatrix(){
                if(conMatrix_was_computed==true){
                    // Clear and initialize the vector. Then copy the info from the connectivity matrix
                    edgeList_destruction();

                    numType costAux;
                    for(int i=0; i<size; ++i){
                        edgeList.push_back(vector<int_and_num_Pair<numType>>());
                        for(int j=0; j<size; ++j){
                            if(connectivityMatrix[i][j].get_bool()==true){
                                costAux = connectivityMatrix[i][j].get_value();
                                edgeList[i].push_back(int_and_num_Pair(j, costAux));
                            }
                    }
                }
                    edgeList_was_computed = true;
                    return;
                }else{
                    cout<<"Connectivity matrix has not been generated yet, so Edge list can't be generated from it!."
                    <<endl;
                    return;
                }
            }

            int V() const{ // Returns the number of vertices or nodes of the graph
                return size;
            }

            int E() const{ // Returns the number of edges of the graph
                int count = 0;
                if(edgeList_was_computed==true){
                    for(int i=0; i<size; ++i){
                        count += edgeList[i].size();
                    }
                    return count;
                }else if (conMatrix_was_computed==true)
                {
                    for(int i=0; i<size; ++i){
                        for(int j=0; j<size; ++j){
                            if(connectivityMatrix[i][j].get_bool()==true){
                                ++count;
                            }
                        }
                    }
                    return count;
                }else{
                    cout<<"Neither connectivity matrix nor edge list have been computed. Graph is empty!"<<endl;
                    return -1;
                }
            }

            bool adjacent(int nodeFrom, int nodeTo){ // Returns true if there's adjacency from a node "From" to another node "To"
                if(edgeList_was_computed==true){
                    for(int j=0; j<edgeList[nodeFrom].size(); ++j){
                        if(edgeList[nodeFrom][j].get_value1()==nodeTo){
                            return true;
                        }
                    }
                    return false;
                }else if(conMatrix_was_computed==true){
                    if(connectivityMatrix[nodeFrom][nodeTo].get_bool()==true){
                        return true;
                    }else{
                        return false;
                    }
                }else{
                    cout<<"Neither Connectivity matrix nor Edge list was computed. Returning false."<<endl;
                    return false;
                }
            }

            vector<int_and_num_Pair<numType>> neighbors(int nodeFrom){ // Lists the nodes to which we can go from "nodeFrom", along with the costs
                if(edgeList_was_computed==true){
                    return edgeList[nodeFrom];
                }else if(conMatrix_was_computed==true){
                    vector<int_and_num_Pair<numType>> output;
                    numType costAux;
                    for(int j=0; j<size; ++j){
                        if(connectivityMatrix[nodeFrom][j].get_bool()==true){
                            costAux = connectivityMatrix[nodeFrom][j].get_value();
                            output.push_back(int_and_num_Pair(j, costAux));
                        }
                    }
                    return output;
                }else{
                    cout<<"Neither Connectivity matrix nor Edge list was computed. Returning empty vector."<<endl;
                    return vector<int_and_num_Pair<numType>>();
                }
            }

            numType get_node_value(int i) const{ // Returns the value associated with the node i
                return nodeValues[i];
            }

            void set_node_value(int node, numType val){ // Sets the value associated with the node "node" to val
                // If the node values vector has not been initialized yet, initialize it:
                if(nodeValues.size()==0){
                    for(int i=0; i<size; ++i){
                        nodeValues.push_back(0);
                    }
                }

                nodeValues[node] = val;
                return;
            }

            int get_node_tag(int i) const{ // Returns the tag of the node i
                return nodeTags[i];
            }

            void set_node_tag(int node, int val){ // Sets the taf of the node "node" to val
                // If the node tags vector has not been initialized yet, initialize it:
                if(nodeTags.size()==0){
                    for(int i=0; i<size; ++i){
                        nodeTags.push_back(0);
                    }
                }

                nodeTags[node] = val;
                return;
            }

            numType get_edge_value(int nodeFrom, int nodeTo) const{ // Returns the value (the cost) associated to the edge from nodeFrom to nodeTo
                if(edgeList_was_computed==true){
                    bool edgeFound = false;
                    numType costVal = 0;
                    for(int j=0; j<edgeList[nodeFrom].size(); ++j){
                        if(edgeList[nodeFrom][j].get_value1()==nodeTo){
                            edgeFound = true;
                            costVal = edgeList[nodeFrom][j].get_value2();
                            return costVal;
                        }
                    }
                    cout<<"Edge from node "<<nodeFrom<<" to node "<<nodeTo<<" doesn't exist."<<endl;
                    return costVal;
                }else if(conMatrix_was_computed==true){
                    if(connectivityMatrix[nodeFrom][nodeTo].get_bool()==true){
                        return connectivityMatrix[nodeFrom][nodeTo].get_value();
                    }else{
                        cout<<"Edge from node "<<nodeFrom<<" to node "<<nodeTo<<" doesn't exist."<<endl;
                        return 0;
                    }
                }else{
                    cout<<"Neither connectivity matrix nor edge list have been computed. Graph is empty!"<<endl;
                    return 0;
                }
            }

            void print_connectivity_matrix(){
                cout<<"\nPrinting connectivity matrix:"<<endl;
                cout<<"- - - - - - - - - - - - - - -"<<endl;
                cout<<"This shows the connections, and also the (value of the costs)."<<endl;
                cout<<"Connectivity matrix has to be interpreted as follows:"<<endl;
                cout<<"  Row is 'from' and column is 'can go to'. So the element (i,j), being i the row and"<<endl;
                cout<<"  j the column, is be true if node i can go to node j and false otherwise."<<endl;
                cout<<"- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -\n"<<endl;
                if(conMatrix_was_computed==true){
                    int a1=0;
                    unsigned int a2=0;
                    signed int a3=0;
                    short int a4=0;
                    unsigned short int a5=0;
                    signed short int a6=0;
                    long int a7=0;
                    signed long int a8=0;
                    unsigned long int a9=0;
                    long long int a10=0;
                    unsigned long long int a11=0;
                    numType checker = connectivityMatrix[0][0].get_value();
                    if(typeid(checker).name()==typeid(a1).name()||\
                    typeid(checker).name()==typeid(a2).name()||typeid(checker).name()==typeid(a3).name()||\
                    typeid(checker).name()==typeid(a4).name()||typeid(checker).name()==typeid(a5).name()||\
                    typeid(checker).name()==typeid(a6).name()||typeid(checker).name()==typeid(a7).name()||\
                    typeid(checker).name()==typeid(a8).name()||typeid(checker).name()==typeid(a9).name()||\
                    typeid(checker).name()==typeid(a10).name()||typeid(checker).name()==typeid(a11).name()){
                        cout<<"      ";
                        for(int j=0; j<size; ++j){
                            printf("     %4d:", j);
                        }
                        cout<<endl;
                        for(int i=0; i<size; ++i){
                            printf("%4d: ", i);
                            for(int j=0; j<size; ++j){
                                printf(" %4d(%3d)", connectivityMatrix[i][j].get_bool(), connectivityMatrix[i][j].get_value());
                            }
                            cout<<""<<endl;
                        }
                    }else{
                        cout<<"      ";
                        for(int j=0; j<size; ++j){
                            printf("          %4d:", j);
                        }
                        cout<<endl;
                        for(int i=0; i<size; ++i){
                            printf("%4d: ", i);
                            for(int j=0; j<size; ++j){
                                printf(" %4d(%8.4f)", connectivityMatrix[i][j].get_bool(), connectivityMatrix[i][j].get_value());
                            }
                            cout<<""<<endl;
                        }
                    }
                    cout<<"\n"<<endl;
                    return;
                }else{
                    cout<<"Connectivity matrix has not been computed yet!"<<endl;
                    return;
                }
            }

            void print_edge_list(){
                cout<<"\nPrinting edge list:"<<endl;
                cout<<"- - - - - - - - - - - - - - -"<<endl;
                cout<<"This list contains the connections and also the (value of the costs)."<<endl;
                cout<<"Edge list has to be interpreted as follows:"<<endl;
                cout<<"   This is a vector of vectors. It contains a subvector for each of the nodes."<<endl;
                cout<<"   The subvector of each node contains those nodes to which we can go from the current node."<<endl;
                cout<<"- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -\n"<<endl;
                if(edgeList_was_computed==true){
                    for(int i=0; i<size; ++i){
                        cout<<"Node "<<i<<":";
                        for(int j=0; j<edgeList[i].size(); ++j){
                            cout<<" "<<edgeList[i][j].get_value1()<<"("<<edgeList[i][j].get_value2()<<")";
                            if(j<edgeList[i].size()-1){
                                cout<<",";
                            }
                        }
                        cout<<""<<endl;
                    }

                    cout<<""<<endl;
                    return;
                }else{
                    cout<<"Edge list has not been computed yet!"<<endl;
                    return;
                }
            }

            vector<vector<bool_and_num_Pair<numType>>> get_connectivityMatrix(){
                if(conMatrix_was_computed == false){
                    cout<<"Connectivity matrix hadn't been computed yet, but it's now being generated."<<endl;
                    generate_conMatrix_from_edgeList();
                }
                return connectivityMatrix;
            }

            vector<vector<int_and_num_Pair<numType>>> get_edgeList(){
                if(edgeList_was_computed == false){
                    cout<<"Edge list hadn't been computed yet, but it's now being generated."<<endl;
                    generate_edgeList_from_conMatrix();
                }
                return edgeList;
            }

        private: // These methods are needed in the copy constructor
            vector<vector<bool_and_num_Pair<numType>>> private_getConMatrix() const{return connectivityMatrix;}
            vector<vector<int_and_num_Pair<numType>>> private_getEdgeList() const{return edgeList;}
            representationMode get_preferredRepresentation() const{return preferredRepresentation;}
            vector<numType> get_nodeValues() const{return nodeValues;}
            vector<int> get_nodeTags() const{return nodeTags;}
            bool get_conMatrixWasComputed() const{return conMatrix_was_computed;}
            bool get_edgeListWasComputed() const{return edgeList_was_computed;}

        protected:
            // Common members for the derived classes:
            // =======================================
            int const size;
            vector<vector<bool_and_num_Pair<numType>>> connectivityMatrix; // Think of it as a 2D matrix. First dimension
            // will be rows and second dimension will be columns
            // This matrix will contain the connections AND ALSO THE VALUE OF THE COSTS.
            // Connectivity matrix has to be interpreted as follows:
            //      Row is "from" and column is "can go to". So the element (i,j), being i the row and
            //      j the column, will be true if node i can go to node j and false otherwise.
            vector<vector<int_and_num_Pair<numType>>> edgeList; // Think of it as a vector of vectors
            // This list will contain the connections AND ALSO THE VALUE OF THE COSTS.
            // Edge list has to be interpreted as follows:
            //      This is a vector of vectors. It contains a subvector for each of the nodes.
            //      The subvector of each node contains those nodes to which we can go from the current node.
            representationMode preferredRepresentation;
            vector<numType> nodeValues; // A vector containing the values assigned to the nodes
            vector<int> nodeTags; // A vector containing int tags for the nodes, in case they are needed
            // By default, the tag of a node will be 0
            bool conMatrix_was_computed;
            bool edgeList_was_computed;
    };
    
    // ===============================================================================================
    // derived class undirected_Graph
    // ===============================================================================================
    template<typename numType>
    class undirected_Graph : public Graph<numType>{
        // It is similar to a directed graph, but with its connectivity matrix and edge list being symmetric
        protected:
            // Special constructor only for use by the derived class Hex_Board (doesn't generate the matrix
            // nor the edge list). The parameter "dummy" is needed just to have a different signature for this
            // special constructor
            undirected_Graph(int size, string dummy, representationMode mode=CON_MATRIX):\
            Graph<numType>(size,mode),density(0){
                // Don't generate the connectivity matrix nor the edge list (as required
                // by the derived class Hex_Board)
                
                // Initialize the node values:
                for(int i=0; i<this->size; ++i){this->nodeValues.push_back(0);}
                // Initialize the node tags:
                for(int i=0; i<this->size; ++i){this->nodeTags.push_back(0);}
            }
        
        public:
            // Constructors (standard and with parameters):
            // ============================================
            // Standard constructor. Construct a graph of size 5 and density 1.0
            undirected_Graph():Graph<numType>(5,CON_MATRIX),density(1.0){
                // Generate the connectivity matrix or the edge list:
                if(this->preferredRepresentation==CON_MATRIX){generate_graph_matrixMode();}
                else{generate_graph_edgeListMode();}
                // Initialize the node values:
                for(int i=0; i<this->size; ++i){this->nodeValues.push_back(0);}
                // Initialize the node tags:
                for(int i=0; i<this->size; ++i){this->nodeTags.push_back(0);}
            }
            // Size and density as parameters. Default value for density if not given
            undirected_Graph(int size, float density=1.0, representationMode mode=CON_MATRIX):\
            Graph<numType>(size,mode),density((density>=0 && density<=1.0)?density:1.0){
                // Generate the connectivity matrix or the edge list:
                if(this->preferredRepresentation==CON_MATRIX){generate_graph_matrixMode();}
                else{generate_graph_edgeListMode();}
                // Initialize the node values:
                for(int i=0; i<this->size; ++i){this->nodeValues.push_back(0);}
                // Initialize the node tags:
                for(int i=0; i<this->size; ++i){this->nodeTags.push_back(0);}
            }
            // Node values and density as parameters. Default density if not given
            undirected_Graph(vector<numType> nodeValues, float density=1.0, representationMode mode=CON_MATRIX):\
            Graph<numType>(nodeValues.size(),mode,nodeValues),\
            density((density>=0 && density<=1.0)?density:1.0){
                // Generate the connectivity matrix or the edge list:
                if(this->preferredRepresentation==CON_MATRIX){generate_graph_matrixMode();}
                else{generate_graph_edgeListMode();}
                // Initialize the node tags:
                for(int i=0; i<this->size; ++i){this->nodeTags.push_back(0);}
            }

            // Copy constructor:
            undirected_Graph(const undirected_Graph<numType>& sample):Graph<numType>(sample),density(sample.get_density()){}

            // Class methods:
            // ==============
            virtual void generate_graph_matrixMode(){
                if(this->conMatrix_was_computed==true){
                    cout<<"Connectivity matrix is already computed. Nothing new has been done."<<endl;
                    return;
                }
                bool boolAux;
                double doubleAux;
                numType costAux;
                for(int i=0; i<this->size; ++i){ // Iterating rows
                    this->connectivityMatrix.push_back(vector<bool_and_num_Pair<numType>>());
                    for(int j=0; j<this->size; ++j){ // Iterating columns
                        if(i<j){
                            doubleAux = probability_having_edge(gen);
                            boolAux = (doubleAux<density);
                            if(boolAux==true){
                                costAux = static_cast<numType>(cost_value(gen));
                            }else{
                                costAux = 0;
                            }
                            this->connectivityMatrix[i].push_back(bool_and_num_Pair(boolAux, costAux));

                        }else if(i==j){ // Skip i==j, to avoid connecting a node with itself
                            boolAux = false;
                            costAux = 0;
                            this->connectivityMatrix[i].push_back(bool_and_num_Pair(boolAux, costAux));
                        }else{ // Undirected graph, so the matrix has to be symmetric
                            boolAux = this->connectivityMatrix[j][i].get_bool();
                            costAux = this->connectivityMatrix[j][i].get_value();
                            this->connectivityMatrix[i].push_back(bool_and_num_Pair(boolAux, costAux));
                        }
                    }
                }
                cout<<"Connectivity matrix has been generated."<<endl;
                this->conMatrix_was_computed = true;
                return;
            }

            virtual void generate_graph_edgeListMode(){
                // This method has to take into account the symmetry too. If node
                // x has node y in its list, node y has to have node x too.
                // To do that, the most efficient way is to build directly the
                // connectivity matrix and then compute the edge list from the matrix
                generate_graph_matrixMode();
                this->generate_edgeList_from_conMatrix();
                cout<<"Edge list has been generated."<<endl;
                this->edgeList_was_computed = true;
                return;
            }

            void force_set_edge_value(int nodeFrom, int nodeTo, numType val){ // Sets (OVERRIDING it!!) the cost of the edge from nodeFrom
            // to nodeTo to val if the edge already exists. If it doesn't exist, the edge is added.
            // This method has to take into account the symmetry too!
                if(this->edgeList_was_computed==true){
                    // Check if the edge already exists and if so, impose the new value.
                    // If it doesn't exist, add the new edge and its value.
                    bool alreadyExists = false;
                    for(int j=0; j<this->edgeList[nodeFrom].size(); ++j){
                        if(this->edgeList[nodeFrom][j].get_value1()==nodeTo){
                            alreadyExists = true;
                            this->edgeList[nodeFrom][j].set_value2(val);

                            // And now, set the symmetric edge:
                            for(int k=0; k<this->edgeList[nodeTo].size(); ++k){
                                if(this->edgeList[nodeTo][k].get_value1()==nodeFrom){
                                    this->edgeList[nodeTo][k].set_value2(val);
                                    break;
                                }
                            }

                            break;
                        }
                    }
                    if(alreadyExists==false){
                        this->edgeList[nodeFrom].push_back(int_and_num_Pair(nodeTo, val));
                        // And now, set the symmetric edge:
                        this->edgeList[nodeTo].push_back(int_and_num_Pair(nodeFrom, val));
                    }
                }
                if(this->conMatrix_was_computed==true){
                    this->connectivityMatrix[nodeFrom][nodeTo].set_bool(true);
                    this->connectivityMatrix[nodeFrom][nodeTo].set_value(val);
                    // And now, set the symmetric edge:
                    this->connectivityMatrix[nodeTo][nodeFrom].set_bool(true);
                    this->connectivityMatrix[nodeTo][nodeFrom].set_value(val);
                }
                return;
            }

            void addEdge(int nodeFrom, int nodeTo, numType cost){ // Adds an edge (if it doesn't exist yet) and adds its cost
            // This method has to take into account the symmetry too!
                if(this->edgeList_was_computed==true){
                    // Add the new edge and its cost ONLY IF THE EDGE DOESN'T EXIST YET.
                    bool alreadyExists = false;
                    for(int j=0; j<this->edgeList[nodeFrom].size(); ++j){
                        if(this->edgeList[nodeFrom][j].get_value1()==nodeTo){
                            alreadyExists = true;
                            break;
                        }
                    }
                    if(alreadyExists==false){
                        this->edgeList[nodeFrom].push_back(int_and_num_Pair(nodeTo, cost));
                        // And now, set the symmetric edge:
                        this->edgeList[nodeTo].push_back(int_and_num_Pair(nodeFrom, cost));
                    }
                }
                if(this->conMatrix_was_computed==true){
                    // Add the new edge and its cost ONLY IF THE EDGE DOESN'T EXIST YET.
                    if(this->connectivityMatrix[nodeFrom][nodeTo].get_bool()==false){
                        this->connectivityMatrix[nodeFrom][nodeTo].set_bool(true);
                        this->connectivityMatrix[nodeFrom][nodeTo].set_value(cost);
                        // And now, set the symmetric edge:
                        this->connectivityMatrix[nodeTo][nodeFrom].set_bool(true);
                        this->connectivityMatrix[nodeTo][nodeFrom].set_value(cost);
                    }
                }
                return;
            }

            void deleteEdge(int nodeFrom, int nodeTo){ // Removes the edge from nodeFrom to nodeTo, if it exists
            // This method has to take into account the symmetry too!
                if(this->edgeList_was_computed==true){
                    // Delete the edge if it is found.
                    bool found = false;
                    for(int j=0; j<this->edgeList[nodeFrom].size(); ++j){
                        if(this->edgeList[nodeFrom][j].get_value1()==nodeTo){
                            found = true;
                            this->edgeList[nodeFrom].erase(this->edgeList[nodeFrom].begin()+j);
                                // https://cplusplus.com/reference/vector/vector/erase/
                                // (vector.erase(vector.begin()+n) removes the element with index n and relocates memory)
                                // (vector.erase(vector.begin()+ini, vector.begin()+fin) removes the elements with indices in the range [ini,fin) and relocates memory)
                            
                            // And now, erase the symmetric edge:
                            for(int k=0; k<this->edgeList[nodeTo].size(); ++k){
                                if(this->edgeList[nodeTo][k].get_value1()==nodeFrom){
                                    this->edgeList[nodeTo].erase(this->edgeList[nodeTo].begin()+k);
                                    break;
                                }
                            }
                            
                            break;
                        }
                    }
                }
                if(this->conMatrix_was_computed==true){
                    // Delete the edge if it is found.
                    if(this->connectivityMatrix[nodeFrom][nodeTo].get_bool()==true){
                        this->connectivityMatrix[nodeFrom][nodeTo].set_bool(false);
                        this->connectivityMatrix[nodeFrom][nodeTo].set_value(0);
                        // And now, delete the symmetric edge:
                        this->connectivityMatrix[nodeTo][nodeFrom].set_bool(false);
                        this->connectivityMatrix[nodeTo][nodeFrom].set_value(0);
                    }
                }
                return;
            }

            float get_density() const{
                return this->density;
            }

        private:
            float const density;
    };

    // ===============================================================================================
    // derived class Hex_Board. It's a kind of undirected Graph
    // ===============================================================================================
    class Hex_Board : public undirected_Graph<int>{
        // The Hex board will have border length N (that is the length of the borders of the table),
        // that is, N*N nodes or squares (the graph will have size N*N). A node of the board is
        // identified by its index (from 0 to N*N - 1) and has associated a position i,j or x,y,
        // where x means "row" and y means "column". x is 0 at top border and N-1 at bottom border.
        // y is 0 at left border and N-1 at right border.
        //
        //    y ->
        //  x
        //  |    0,0    ...    0,N-1
        //  v
        //         .     .        .
        //          .       .      .
        //           .         .    .
        //
        //          N-1,0   ...    N-1,N-1

        // =====================================
        // NOTE: Player 1 is X and player 2 is O
        // =====================================

        public:
            // Constructors (default and with parameters):
            // ===========================================
            // Notice that the variable "density" is not representative and inaccesible for this class.
            
            // Default constructor. Construct an Hex board of border length 11
            Hex_Board():undirected_Graph<int>(11*11,"dummy_string",CON_MATRIX),border_length(11){
                generate_blank_connected_board();
            }// Rememember that a board with edges of length N has N^2 nodes!

            // Border length of the board as a parameter. Default is 11
            Hex_Board(int border_length=11, representationMode repr_mode=CON_MATRIX):\
            undirected_Graph<int>(border_length*border_length,"dummy_string",repr_mode),border_length(border_length){
                generate_blank_connected_board();
            }// Rememember that a board with edges of length N has N^2 nodes!

            // Copy constructor:
            Hex_Board(const Hex_Board& sample):undirected_Graph<int>(sample),border_length(sample.get_border_length()){}

            // Class specific methods:
            // =======================
            void generate_blank_connected_board(){ // Generates a blank and connected Hex board graph
                if(this->preferredRepresentation==CON_MATRIX){
                    generate_graph_matrixMode();
                }else{
                    generate_graph_edgeListMode();
                }
            }

            // Overridden method. Generates a blank and connected Hex board graph. Matrix mode
            void generate_graph_matrixMode(){
                if(this->conMatrix_was_computed==true){
                    cout<<"Connectivity matrix is already computed. Nothing new has been done."<<endl;
                    return;
                }
                
                // First initialize a connectivity matrix of zeros:
                for(int i=0; i<this->size; ++i){ // Iterating rows
                    this->connectivityMatrix.push_back(vector<bool_and_num_Pair<int>>());
                    for(int j=0; j<this->size; ++j){
                        this->connectivityMatrix[i].push_back(bool_and_num_Pair(false, 0));
                    }
                }

                int cost = 1;
                for(int node=0; node<this->size; ++node){
                    pair<int,int> node_coords = nodeIndex_to_coordinate(node);
                    int x = node_coords.first;
                    int y = node_coords.second;
                    int temp_nodeFrom;

                    if(x==0 && y==0){ // Top left corner
                        // Connect to node (x*border_length + y+1):
                        temp_nodeFrom = x*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y):
                        temp_nodeFrom = (x+1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(x==border_length-1 && y==border_length-1){ // Bottom right corner
                        // Connect to node ((x-1)*border_length + y):
                        temp_nodeFrom = (x-1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y-1):
                        temp_nodeFrom = x*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(x==border_length-1 && y==0){ // Bottom left corner
                        // Connect to node ((x-1)*border_length + y):
                        temp_nodeFrom = (x-1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x-1)*border_length + y+1):
                        temp_nodeFrom = (x-1)*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y+1):
                        temp_nodeFrom = x*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(x==0 && y==border_length-1){ // Top right corner
                        // Connect to node (x*border_length + y-1):
                        temp_nodeFrom = x*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y-1):
                        temp_nodeFrom = (x+1)*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y):
                        temp_nodeFrom = (x+1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(x==0){ // Inner top
                        // Connect to node (x*border_length + y-1):
                        temp_nodeFrom = x*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y+1):
                        temp_nodeFrom = x*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y-1):
                        temp_nodeFrom = (x+1)*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y):
                        temp_nodeFrom = (x+1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(x==border_length-1){ // Inner bottom
                        // Connect to node ((x-1)*border_length + y):
                        temp_nodeFrom = (x-1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x-1)*border_length + y+1):
                        temp_nodeFrom = (x-1)*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y-1):
                        temp_nodeFrom = x*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y+1):
                        temp_nodeFrom = x*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(y==0){ // Inner left
                        // Connect to node ((x-1)*border_length + y):
                        temp_nodeFrom = (x-1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x-1)*border_length + y+1):
                        temp_nodeFrom = (x-1)*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y+1):
                        temp_nodeFrom = x*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y):
                        temp_nodeFrom = (x+1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else if(y==border_length-1){ // Inner right
                        // Connect to node ((x-1)*border_length + y):
                        temp_nodeFrom = (x-1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y-1):
                        temp_nodeFrom = x*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y-1):
                        temp_nodeFrom = (x+1)*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y):
                        temp_nodeFrom = (x+1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        
                    }else{ // General inner node
                        // Connect to node ((x-1)*border_length + y):
                        temp_nodeFrom = (x-1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x-1)*border_length + y+1):
                        temp_nodeFrom = (x-1)*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y-1):
                        temp_nodeFrom = x*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node (x*border_length + y+1):
                        temp_nodeFrom = x*border_length + y+1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y-1):
                        temp_nodeFrom = (x+1)*border_length + y-1;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                        // Connect to node ((x+1)*border_length + y):
                        temp_nodeFrom = (x+1)*border_length + y;
                        this->connectivityMatrix[temp_nodeFrom][node].set_pair(true,cost);
                    }
                }

                cout<<"Connectivity matrix has been generated."<<endl;
                this->conMatrix_was_computed = true;
                return;
            }

            // Overridden method. Generates a blank and connected Hex board graph. Edge list mode
            void generate_graph_edgeListMode(){
                generate_graph_matrixMode();
                this->generate_edgeList_from_conMatrix();
                cout<<"Edge list has been generated."<<endl;
                this->edgeList_was_computed = true;
                return;
            }

            void draw_board_ASCII(bool clear_screen_previously = true){ // Draws the board (in its current status) in ASCII characters
            //       x   x   x   x   x
            //       0   1   2  ... 10
            //  o 0  . - . - . - . - .  0 o
            //        \ / \ / \ / \ / \
            //    o 2  . - . - . - . - .  1 o
            //          \ / \ / \ / \ / \
            //      o 3  . - . - . - O - .  2 o
            //            \ / \ / \ / \ / \
            //      o ...  . - . - X - . - .  ...  o
            //              \ / \ / \ / \ / \
            //         o 10  . - . - . - . - .  10 o
            //               0   1   2  ... 10
            //               x   x   x   x   x
            
            if(clear_screen_previously){ // Printing new lines to scroll, and so clean the screen
                for(int i=0; i<border_length; ++i){
                    cout<<"\n\n\n\n\n\n\n\n\n"<<endl;
                }
            }

            cout<<"      ";
            for(int y=0; y<border_length-1; ++y){cout<<"x   ";}
                    cout<<"x"<<endl;
            
            cout<<"     ";
            for(int y=0; y<border_length-1; ++y){
                printf("%2d  ", y);
            }
            printf("%2d\n", border_length-1);

            for(int x=0; x<border_length; ++x){
                for(int k=0; k<x; ++k){cout<<"  ";}
                printf("o %2d  ", x);
                for(int y=0; y<border_length-1; ++y){
                    int aux = get_node_tag_byCoordinates(x,y);
                    if(aux==1){
                        cout<<"X - ";
                    }else if(aux==2){
                        cout<<"O - ";
                    }else{
                        cout<<". - ";
                    }
                }
                int aux = get_node_tag_byCoordinates(x,border_length-1);
                if(aux==1){
                    cout<<"X";
                }else if(aux==2){
                    cout<<"O";
                }else{
                    cout<<".";
                }
                printf(" %2d  o\n", x);
                if(x<border_length-1){
                    for(int k=0; k<=x; ++k){cout<<"  ";}
                    cout<<"     ";
                    for(int y=0; y<border_length-1; ++y){cout<<"\\ / ";}
                    cout<<"\\"<<endl;
                }else{
                    for(int k=0; k<x; ++k){cout<<"  ";}
                    cout<<"     ";
                    for(int y=0; y<border_length-1; ++y){
                        printf("%2d  ", y);
                    }
                    printf("%2d\n", border_length-1);
                    for(int k=0; k<x; ++k){cout<<"  ";}
                    cout<<"      ";
                    for(int y=0; y<border_length-1; ++y){cout<<"x   ";}
                    cout<<"x"<<endl;
                }
            }
            return; 
            }

            void disconnect_node_from_neighbors(int node){ // Breaks the connection of "node" with all of its neighbors
                for(int i=0; i<this->size; ++i){
                    for(int j=0; j<=i; ++j){
                        this->deleteEdge(i,j);
                        // That parent method takes into account the symmetry of undirected graphs,
                        // so that only a half of the graph has to be walked.
                    }
                }
                return;
            }

            int coordinate_to_nodeIndex(int x, int y) const{
                if(x<0 || x>border_length-1 || y<0 || y>border_length-1){
                    cout<<"Coordinates aren't valid. Out of range";
                    return -999;
                }else{
                    return x*border_length+y;
                }
            }

            pair<int, int> nodeIndex_to_coordinate(int index) const{
                if(index<0 || index>this->size-1){
                    pair<int, int> dummy(-999, -999);
                    cout<<"Index isn't valid. Out of range";
                    return dummy;
                }else{
                    int x=0, y=0;
                    x = index / border_length;
                    y = index % border_length;
                    pair<int, int> coordinates(x, y);
                    return coordinates;
                }
            }

            // The following methods for the node tags and the node values are an implementation
            // of those which are in the base class Graph, but now using coordinates. The use of
            // node indices remain available, as the methods of the base class are available too:
            int get_node_value_byCoordinates(int x, int y) const{
                return this->get_node_value(coordinate_to_nodeIndex(x,y));
            }

            void set_node_value_byCoordinates(int x, int y, int val){
                this->set_node_value(coordinate_to_nodeIndex(x,y), val);
                return;
            }

            int get_node_tag_byCoordinates(int x, int y) const{
                return this->get_node_tag(coordinate_to_nodeIndex(x,y));
            }

            void set_node_tag_byCoordinates(int x, int y, int val){
                this->set_node_tag(coordinate_to_nodeIndex(x,y), val);
                return;
            }

            int get_border_length() const{
                return this->border_length;
            }

        private:
            int border_length; // In this class, size means the number of nodes of the graph,
            // and border_length means the length of the borders or sides of the Hex table

    };
   
    // ===============================================================================================
    // class PriorityQueue
    // ===============================================================================================
    template<typename numType>
    class PriorityQueue{
        public:
            PriorityQueue(){} // Default constructor

            ~PriorityQueue(){queue.clear();} // Destructor
        
        void change_Prioirity(int index, int new_position){ // Changes the priority of queue element
            int_int_and_num_Triad<numType> temp;
            temp = queue[index];
            queue.erase(queue.begin()+index);
            queue.insert(queue.begin()+new_position, temp);
            return;
        }

        bool contains(int_int_and_num_Triad<numType> queue_element){ // Does the queue contain queue_element
            for(int i=0; i<queue.size(); ++i){
                if(queue[i].get_value1()==queue_element.get_value1() \
                && queue[i].get_value2()==queue_element.get_value2() \
                && queue[i].get_value3()==queue_element.get_value3()){
                    return true;
                }
            }
            return false;
        }

        bool contains_elem_with_val1_val2(int val1, int val2){ // Does the queue contain an element whose first two values are val1 and val2
            for(int i=0; i<queue.size(); ++i){
                if(queue[i].get_value1()==val1 \
                && queue[i].get_value2()==val2){
                    return true;
                }
            }
            return false;
        }

        bool contains_elem_with_val1(int val1){ // Does the queue contain an element whose first value is val1
            for(int i=0; i<queue.size(); ++i){
                if(queue[i].get_value1()==val1){
                    return true;
                }
            }
            return false;
        }

        bool contains_elem_with_val2(int val2){ // Does the queue contain an element whose second value is val2
            for(int i=0; i<queue.size(); ++i){
                if(queue[i].get_value2()==val2){
                    return true;
                }
            }
            return false;
        }

        bool theres_any_in_queue_not_in_ref(vector<int_int_and_num_Triad<numType>> ref_queue){
            if(queue.size()>0 && ref_queue.size()==0){
                return true;
            }
            bool condition = true;
            for(int i=0; i<queue.size(); ++i){
                for(int j=0; j<ref_queue.size(); ++j){
                    if(ref_queue[j].get_value1()==queue[i].get_value1()&&\
                    ref_queue[j].get_value2()==queue[i].get_value2()&&\
                    ref_queue[j].get_value3()==queue[i].get_value3()){
                        condition = false;
                        break;
                    }
                }
                if(condition==false){
                    break;
                }
            }
            return condition;
        }

        int_int_and_num_Triad<numType> get_first_in_queue_not_in_ref_NotDelete(vector<int_int_and_num_Triad<numType>> ref_queue){
            if(queue.size()>0 && ref_queue.size()==0){
                return queue[0];
            }
            bool aux = false;
            for(int i=0; i<queue.size(); ++i){
                for(int j=0; j<ref_queue.size(); ++j){
                    if(ref_queue[j].get_value1()==queue[i].get_value1()&&\
                    ref_queue[j].get_value2()==queue[i].get_value2()&&\
                    ref_queue[j].get_value3()==queue[i].get_value3()){
                        aux = true;
                        break;
                    }
                }
                if(aux==false){
                    return queue[i];
                }
            }
            return int_int_and_num_Triad<numType>(-1, -1, static_cast<numType>(-1));
        }

        int_int_and_num_Triad<numType> getAndDelete_first_in_queue_not_in_ref(vector<int_int_and_num_Triad<numType>> ref_queue){
            if(queue.size()>0 && ref_queue.size()==0){
                int_int_and_num_Triad<numType> temp = queue[0];
                queue.erase(queue.begin());
                return temp;
            }
            bool aux = false;
            for(int i=0; i<queue.size(); ++i){
                for(int j=0; j<ref_queue.size(); ++j){
                    if(ref_queue[j].get_value1()==queue[i].get_value1()&&\
                    ref_queue[j].get_value2()==queue[i].get_value2()&&\
                    ref_queue[j].get_value3()==queue[i].get_value3()){
                        aux = true;
                        break;
                    }
                }
                if(aux==false){
                    int_int_and_num_Triad<numType> temp = queue[i];
                    queue.erase(queue.begin()+i);
                    return temp;
                }
            }
            return int_int_and_num_Triad<numType>(-1, -1, static_cast<numType>(-1));
        }

        void insert(int_int_and_num_Triad<numType> new_element){ // Insert new_element into the queue.
        // It will be inserted respecting the increasing order of cost in the queue.
            if(queue.size()==0){
                queue.push_back(new_element);
                return;
            }
            for(int i=0; i<queue.size(); ++i){
                if(queue[i].get_value3()>=new_element.get_value3()){
                    queue.insert(queue.begin()+i, new_element);
                    return;
                }
            }
            queue.push_back(new_element);
            return;
        }

        int_int_and_num_Triad<numType> get_top_NotDelete(){ // Returns the top element of the queue
            return queue[0];
        }

        int_int_and_num_Triad<numType> get_top_and_delete(){ // Returns the top element of the queue
        // and deletes it from the queue
            int_int_and_num_Triad<numType> temp;
            temp = queue[0];
            queue.erase(queue.begin());
            return temp;
        }

        int_int_and_num_Triad<numType> get_element_n_NotDelete(int n){ // Returns the nth element of the queue
            return queue[n];
        }

        int_int_and_num_Triad<numType> get_element_n_and_delete(int n){ // Returns the nth element of the queue
        // and deletes it from the queue
            int_int_and_num_Triad<numType> temp;
            temp = queue[n];
            queue.erase(queue.begin()+n);
            return temp;
        }

        void delete_top(){ // Removes the top element from the queue
            queue.erase(queue.begin());
            return;
        }

        int size(){ // Returns the number of queue_elements
            return queue.size();
        }

        bool improves_cost_of_node(int_int_and_num_Triad<numType> new_element){ // Returns bool only if
        // the new_element has LESS total cost, for its nodeTo (the second value of the triad), than
        // all of the existing elements which contain that nodeTo.
            for(int i=0; i<queue.size(); ++i){
                if(queue[i].get_value2()==new_element.get_value2() \
                && queue[i].get_value3()<=new_element.get_value3()){
                    return false;
                }
            }
            return true;
        }

        void update_queue_with_shorter_path(int_int_and_num_Triad<numType> new_element){
            for(int i=0; i<queue.size(); ++i){
                for(int k=0; k<queue.size(); ++k){
                    if(queue[k].get_value2()==new_element.get_value2()){
                        queue.erase(queue.begin()+k);
                        break;
                    }
                }
            }
            insert(new_element);
            return;
        }

        private:
            vector<int_int_and_num_Triad<numType>> queue;
    };
    
    // ===============================================================================================
    // class ShortestPath
    // ===============================================================================================
    template<typename graphType, typename numType>
    class ShortestPath{

        public:
            // Constructor:
            ShortestPath(graphType& graph):graph(graph),path_was_seeked(false),path_exists(false),\
            nodeFrom(0),nodeTo(0),nodeTo_was_visited(false),terminated(false),\
            shortest_path_cost(numeric_limits<numType>::infinity()>numeric_limits<numType>::max()?numeric_limits<numType>::infinity():numeric_limits<numType>::max()){}
            // Notice that graph is passed as a & type, in order to use pass-by-breference and so
            // we are not copying the object but using the original object. We could have marked it
            // as constant (const graphType& graph) to avoid the original object being changed, but
            // here we prefer to save the changes (for example, if we compute the Edge list from
            // the Connectivity matrix we want to keep the newly computed Edge list on the original
            // object too). When declaring the variable, under "public" below  we have to use "&"
            // there too!

            // Destructor:
            ~ShortestPath(){
                open_set.clear();
                closed_set.clear();
                tentative_costs.clear();
                neighbors.clear();
                used_queue_elements.clear();
                shortest_path.clear();
                raw_shortest_path.clear();
            }

            bool i_is_in_vector(int i, vector<int> _vector){
                bool result = false;
                for(int k : _vector){
                    if(k==i){
                        result = true;
                        break;
                    }
                }
                return result;
            }
            
            void seek_path(int _nodeFrom, int _nodeTo, vector<int> avoid_nodes_with_these_tags=vector<int>()){
                // This is the implementation of Dijkstra's algorithm

                // Those nodes whose tag is contained in avoid_nodes_with_these_tags will not be considered
                // for the possible paths

                // First, clear variables in case a prior computation has been done on this object:
                if(path_was_seeked==true){
                    open_set.clear();
                    closed_set.clear();
                    tentative_costs.clear();
                    neighbors.clear();
                    used_queue_elements.clear();
                    shortest_path.clear();
                    raw_shortest_path.clear();
                    path_was_seeked = false;
                    terminated = false;
                    path_exists = false;
                    nodeTo_was_visited = false;
                    queue = PriorityQueue<numType>();
                    last_top_of_queue = int_int_and_num_Triad<numType>();
                    shortest_path_cost = 0;
                }

                // Set these two variables:
                nodeFrom = _nodeFrom;
                nodeTo = _nodeTo;

                // Now mark those nodes which are banned
                vector<int> banned_nodes;
                for(int i=0; i<graph.V(); ++i){
                    int tag_read = graph.get_node_tag(i);
                    for(int banned_tag : avoid_nodes_with_these_tags){
                        if(tag_read==banned_tag){
                            banned_nodes.push_back(i);
                            break;
                        }
                    }
                }
                // If nodeFrom or nodeTo are in banned_nodes, no path can be computed. Return:
                for(int node : banned_nodes){
                    if(node==nodeFrom || node==nodeTo){
                        // cout<<"\nNo path can be computed because the source node or the destination node are prohibited nodes!"<<endl;
                        terminated = true;
                        path_was_seeked = true;
                        path_exists = false;
                        return;
                    }
                }
                
                // Begin computation:

                // Label all of the not banned nodes, except for nodeFrom, as unvisited:
                for(int i=0; i<graph.V(); ++i){
                    if(!i_is_in_vector(i,banned_nodes)){
                        if(i!=nodeFrom){
                            open_set.push_back(i);
                        }else{
                            closed_set.push_back(i);
                        }
                    }
                }

                // Set tentative costs to infinity, except for the nodeFrom's which is zero:
                for(int i=0; i<graph.V(); ++i){
                    if(i!=nodeFrom){
                        tentative_costs.push_back(numeric_limits<numType>::infinity()>numeric_limits<numType>::max()?numeric_limits<numType>::infinity():numeric_limits<numType>::max());
                    }else{
                        tentative_costs.push_back(0);
                    }
                }

                // Begin iterating.
                terminated = false;
                currentNode = nodeFrom;
                while(terminated == false){
                    // Locate the current node's neighbors:
                    neighbors = graph.neighbors(currentNode);
                    // Add to the priority queue (this is done in increasing order) those neighbours
                    // of currentNode which are in the open set:
                    for(int i=0; i<neighbors.size(); ++i){
                        if(find(open_set.begin(), open_set.end(), neighbors[i].get_value1()) != open_set.end() &&\
                        !i_is_in_vector(neighbors[i].get_value1(),banned_nodes)){ // This means
                            // if(neighbors[i].node_number is in open_set and neighbors[i].node_number is not banned)
                            // But before adding those neighbors to the queue, their costs must be updated
                            // to the current total value, by adding the cost of the currentNode up to now !
                            int_and_num_Pair<numType> temp = neighbors[i];
                            temp.set_value2(temp.get_value2() + tentative_costs[currentNode]);
                            int_int_and_num_Triad<numType> triad = join_current_and_neighbor_and_cost(currentNode, temp);
                            // Important: We must add the element to the queue if it improves the total cost towards
                            // a new node. If that node is already with less or equal cost in the queue, don't add it.
                            // But if it was in the queue with more cost, add the new one and delete the old one (update the queue)
                            if(queue.contains_elem_with_val1_val2(triad.get_value1(), triad.get_value2())==false\
                            && queue.improves_cost_of_node(triad)){
                                queue.update_queue_with_shorter_path(triad);
                            }
                        }
                    }
                    // What happens if the currentNode doesn't have neigbors, nor has neighbors which are in the
                    // open set, nor has neighbours which are in the open set and improve the cost?
                    // --> Just nothing is added to the queue in this iteration

                    // Now we choose the "To" node in the priority queue which has the least cost. That is
                    // the top of the queue. We mark that node as current node for the next iteration.
                    // we remove that element from the queue and we move that node from the open set to the
                    // closed set. We also update the cost of that node up to now, by updating the value stored
                    // in tentative_costs whit that one which the top of the queue contained.
                    // Additionally, evaluate the terminating condition in order to know if the shortest path has been reached!
                    if(queue.size()>0 && queue.theres_any_in_queue_not_in_ref(used_queue_elements)){
                        int_int_and_num_Triad<numType> aux_top_of_queue = queue.get_first_in_queue_not_in_ref_NotDelete(used_queue_elements);
                        if(aux_top_of_queue.get_value2()!=nodeTo){
                            // We must not move the nodeTo
                            // to the closed_set even if we are to reach it in this iteration, because
                            // even having visited it, there may be other shorter paths that have to
                            // be tested and exhausted.
                            // Furthermore, if the upcoming node is nodeTo, the special code of the
                            // else{} must be used, not this block.
                            int_int_and_num_Triad<numType> another_aux_element = queue.getAndDelete_first_in_queue_not_in_ref(used_queue_elements);
                            used_queue_elements.push_back(another_aux_element);
                            last_top_of_queue = another_aux_element;
                            currentNode = last_top_of_queue.get_value2();
                            for(int i=0; i<open_set.size(); ++i){
                                if(open_set[i]==currentNode){ 
                                    open_set.erase(open_set.begin()+i);
                                    closed_set.push_back(currentNode);
                                    break;
                                }
                            }
                            tentative_costs[currentNode] = last_top_of_queue.get_value3();
                        }else{
                            nodeTo_was_visited = true;
                            int_int_and_num_Triad<numType> another_aux_element\
                            = queue.get_first_in_queue_not_in_ref_NotDelete(used_queue_elements); // DON'T use delete, to be able to know afterwards
                            // that this element of the queue has been used
                            used_queue_elements.push_back(another_aux_element);
                            last_top_of_queue = another_aux_element; // DON'T use delete, to be able to know afterwards
                            // that this element of the queue has been used
                            tentative_costs[currentNode] = last_top_of_queue.get_value3(); // Updates
                            // the tentative cost of the nodeTo
                            // Now, we have to focus on the next element of the queue (if it exists. If not,
                            // we have terminated) to see which node has to be the currentNode. Set that
                            // current node and proceed to the next iteration.
                            if(queue.size()>0 && queue.theres_any_in_queue_not_in_ref(used_queue_elements)){
                                currentNode = queue.get_first_in_queue_not_in_ref_NotDelete(used_queue_elements).get_value1();
                                // Now, for the next iteration we have to avoid to enter on a loop, so we mustn't
                                // add to the priority queue the neighbours that we have already added, and we
                                // mustn't revisit the paths we have already run.
                            }else{
                                terminated = true;
                                path_exists = true;
                            }
                        }
                    }else{ // We have exhausted the potential shorter paths and we can't continue.
                    // If up to this point the nodeTo has been visited, the path exists and the algorithm
                    // has finished. Otherwise, no path from nodeFrom to nodeTo exists!
                        terminated = true;
                        if(nodeTo_was_visited){
                            path_exists = true;
                        }else{
                            path_exists = false;
                        }
                    }
                }
                path_was_seeked = true;

                // Now, reproduce the path found (if it exists) and store it
                if(path_exists==true){
                    reproduce_found_path();
                }
                return;
            }

            bool get_path_was_seeked(){
                return path_was_seeked;
            }

            bool get_path_exists(){
                return path_exists;
            }

            void print_path(){
                if(path_was_seeked==true){
                    if(path_exists==true){
                        cout<<"\n### Shortest path from node "<<nodeFrom<<" to node "<<nodeTo<<":"<<endl;   
                        cout<<"    "<<nodeFrom<<" (0) -> ";
                        for(int i=0; i<shortest_path.size(); ++i){
                            cout<<shortest_path[i].get_value1()<<" ("<<shortest_path[i].get_value2()<<")";
                            if(i<shortest_path.size()-1){cout<<" -> ";}
                        }                     
                        cout<<"\n# Total cost of the path: "<<shortest_path_cost<<endl;
                    }else{
                        cout<<"### NO POSSIBLE PATH EXISTS from node "<<nodeFrom<<" to node "<<nodeTo<<" !"<<endl;
                    }
                }else{
                    cout<<"### Shortest path hasn't been seeked yet!"<<endl;
                }
                return;
            }

            vector<int_and_num_Pair<numType>> get_path(){
                if(path_was_seeked==true){
                    if(path_exists==true){
                        return shortest_path;
                    }else{
                        cout<<"NO POSSIBLE PATH EXISTS from node "<<nodeFrom<<" to node "<<nodeTo<<" ! Returning empty vector."<<endl;
                        return vector<int_and_num_Pair<numType>>();
                    }
                }else{
                    cout<<"Shortest path hasn't been seeked yet! Returning empty vector."<<endl;
                    return vector<int_and_num_Pair<numType>>();
                }
            }

            numType get_path_cost(){
                if(path_was_seeked==true){
                    if(path_exists==true){
                        return shortest_path_cost;
                    }else{
                        cout<<"NO POSSIBLE PATH EXISTS from node "<<nodeFrom<<" to node "<<nodeTo<<" ! Returning -1."<<endl;
                        return -1;
                    }
                }else{
                    cout<<"Shortest path hasn't been seeked yet! -1"<<endl;
                    return -1;
                }
            }

        private:
            int_int_and_num_Triad<numType>
            join_current_and_neighbor_and_cost(int currentNode, int_and_num_Pair<numType> neighbor){
                return int_int_and_num_Triad<numType>(currentNode, neighbor.get_value1(), neighbor.get_value2());
            }

            void reproduce_found_path(){
                // This method examines the vector of used elements of the queue and
                // extracts the steps done, looking in reverse node order (from nodeTo to
                // nodeFrom) and choosing those of least total cost. This way, we have
                // a vector which has, in order, the nodes which conform the shortest path.
                vector<PriorityQueue<numType>> elements_of_each_destination_node;
                for(int i=0; i<graph.V(); ++i){ // (graph.V() returns the size of the graph)
                    elements_of_each_destination_node.push_back(PriorityQueue<numType>());
                    for(int k=0; k<used_queue_elements.size(); ++k){
                        if(used_queue_elements[k].get_value2()==i){
                            elements_of_each_destination_node[i].insert(used_queue_elements[k]);
                        }
                    }
                }
                // Now, we have to iterate through elements_of_each_destination_node, starting on
                // elements_of_each_destination_node[nodeTo] and using
                // elements_of_each_destination_node[nodeTo].get_value1() for next element, and so on:
                currentNode = nodeTo;
                int_int_and_num_Triad<numType> rawAux;
                while(currentNode!=nodeFrom){
                    rawAux = elements_of_each_destination_node[currentNode].get_top_NotDelete();
                    raw_shortest_path.insert(raw_shortest_path.begin(), rawAux); // This is insert at the top
                    currentNode = rawAux.get_value1();
                }
                numType previous_cost = 0;
                numType current_cost = 0;
                numType step_cost = 0;
                for(int i=0; i<raw_shortest_path.size(); ++i){
                    int_and_num_Pair<numType> pairAux;
                    pairAux.set_value1(raw_shortest_path[i].get_value2());
                    current_cost = raw_shortest_path[i].get_value3();
                    step_cost = current_cost - previous_cost;
                    pairAux.set_value2(step_cost);
                    shortest_path.push_back(pairAux);
                    previous_cost = current_cost;
                }
                shortest_path_cost = current_cost;
                return;
            }

        private:
            int nodeFrom;
            int nodeTo;
            int currentNode;
            graphType &graph;
            bool terminated;
            bool path_was_seeked;
            bool path_exists;
            bool nodeTo_was_visited;
            vector<int> open_set; // Set where to store the still UNVISITED nodes
            vector<int> closed_set; // Set where to store the VISITED nodes
            vector<numType> tentative_costs; // Stores the cost it takes from the nodeFrom to each node up to now
            vector<int_and_num_Pair<numType>> neighbors;
            PriorityQueue<numType> queue;
            int_int_and_num_Triad<numType> last_top_of_queue;
            vector<int_int_and_num_Triad<numType>> used_queue_elements; // This will store the elements of the queue which
            // have been used. This is necessary to reproduce the path found, once the algorithm has finished.
            vector<int_and_num_Pair<numType>> shortest_path;
            numType shortest_path_cost;
            vector<int_int_and_num_Triad<numType>> raw_shortest_path; // Auxiliary vector to store the steps of the path before processing them
    };

    // ===============================================================================================
    // class Hex_Game
    // ===============================================================================================
    class Hex_Game{
        // NOTE: Player 1 is X and player 2 is O

        public:
            // Constructors:
            // =============
            Hex_Game(int border_length, int who_starts, bool vs_robot,\
            bool swap_rule):board(Hex_Board(border_length)),border_length(border_length),\
            this_is_movement_number(1),swap_has_been_done(false),\
            game_finished(false),who_won(0),who_starts(who_starts),vs_robot(vs_robot),\
            swap_rule(swap_rule){
                cout<<"Welcome to Hex game!"<<endl;
                cout<<"====================\n"<<endl;
                cout<<"You will be playing on a "<<border_length<<" x "<<border_length<<" board."<<endl;
                cout<<"Game options are set as follow:\n";
                cout<<">> You are PLAYER 1 and your opponent is player 2."<<endl;
                cout<<"   Your symbol is 'X' (up/down). Your opponent is 'O' (left/right)"<<endl;
                cout<<"   Player "<<who_starts<<" will do the first move.\n"<<endl;
                if(vs_robot){
                    cout<<">> Player 2 will be a robot.\n"<<endl;
                }else{
                    cout<<">> Player 2 will be a human.\n"<<endl;
                }
                if(swap_rule){
                    cout<<">> Swap rule is enabled.\n"<<endl;
                }else{
                    cout<<">> Swap rule is not enabled.\n"<<endl;
                }
            }

            Hex_Game(int border_length=11):board(Hex_Board(border_length)),border_length(border_length),\
            this_is_movement_number(1),swap_has_been_done(false),\
            game_finished(false),who_won(0){ // Default constructor
                for(int i=0; i<100; ++i){cout<<endl;} // clearing the screen
                cout<<"Welcome to Hex game!"<<endl;
                cout<<"====================\n"<<endl;
                cout<<"You will be playing on a "<<border_length<<" x "<<border_length<<" board."<<endl;
                cout<<"Now set some options:\n"<<endl;
                cout<<"You are PLAYER 1 and your opponent is player 2."<<endl;
                cout<<"Your symbol is 'X' (up/down). Your opponent is 'O' (left/right)"<<endl;
                cout<<"Who will start (1 or 2)?"<<endl;
                string aux0;
                cin>>aux0;
                if(aux0=="1"){
                    who_starts = 1;
                    cout<<">> Player "<<who_starts<<" will do the first move.\n"<<endl;
                }else if(aux0=="2"){
                    who_starts = 2;
                    cout<<">> Player "<<who_starts<<" will do the first move.\n"<<endl;
                }else{
                    who_starts = 1;
                    cout<<">> Invalid input. Player 1 will do the first move.\n"<<endl;
                }
                string aux;
                cout<<"Do you want to play versus computer (y/n)?"<<endl;
                cin>>aux;
                if(aux=="y" || aux=="Y" || aux=="yes" || aux=="YES" || aux=="Yes"){
                    vs_robot = true;
                    cout<<">> Player 2 will be a robot.\n"<<endl;
                }else if(aux=="n" || aux=="N" || aux=="no" || aux=="NO" || aux=="No"){
                    vs_robot = false;
                    cout<<">> Player 2 will be a human.\n"<<endl;
                }else{
                    vs_robot = true;
                    cout<<">> Invalid input. Player 2 will be a robot.\n"<<endl;
                }
                string aux2;
                cout<<"Do you want to enable the swap rule (y/n)?"<<endl;
                cin>>aux2;
                if(aux2=="y" || aux2=="Y" || aux2=="yes" || aux2=="YES" || aux2=="Yes"){
                    swap_rule = true;
                    cout<<">> Swap rule is enabled.\n"<<endl;
                }else if(aux2=="n" || aux2=="N" || aux2=="no" || aux2=="NO" || aux2=="No"){
                    swap_rule = false;
                    cout<<">> Swap rule is not enabled.\n"<<endl;
                }else{
                    swap_rule = true;
                    cout<<">> Invalid input. Swap rule is enabled.\n"<<endl;
                }
            }

            // Class methods:
            // ==============
            void player_move_by_input(int player){
                bool valid = false;
                bool sub_valid = false;
                string aux;
                int x;
                int y;
                cout<<"\n>>>> Player "<<player<<", choose a square to move."<<endl;
                while(!valid){
                    cout<<">> Enter x coordinate."<<endl;
                    sub_valid = false;
                    while(!sub_valid){
                        cin>>aux;
                        for(int k=0; k<border_length; ++k){
                            if(aux==to_string(k)){
                                sub_valid = true;
                                x = k;
                                break;
                            }
                        }
                        if(!sub_valid){
                            cout<<"-- Invalid input! Enter x coordinate again."<<endl;
                        }
                    }

                    cout<<">> Enter y coordinate."<<endl;
                    sub_valid = false;
                    while(!sub_valid){
                        cin>>aux;
                        for(int k=0; k<border_length; ++k){
                            if(aux==to_string(k)){
                                sub_valid = true;
                                y = k;
                                break;
                            }
                        }
                        if(!sub_valid){
                            cout<<"-- Invalid input! Enter y coordinate again."<<endl;
                        }
                    }

                    int nodeTag = board.get_node_tag_byCoordinates(x,y);
                    if(nodeTag==0){ // Node tag has to be 0 (default). 1 would be a player 1's
                    // previous movement and 2 would be a player 2's previous movement.
                        valid = true;
                    }

                    if(!valid){ // Chosen square corresponds to a previous movement. Illegal movement.
                        cout<<"  >> Illegal movement. Player "<<player<<", please choose another square."<<endl;
                    }
                }
                
                board.set_node_tag_byCoordinates(x,y,player);
                cout<<"Player "<<player<<" has moved.\n"<<endl;

                board.draw_board_ASCII(false);

                if(player==1){
                    player_1_moves.push_back(pair<int,int>(x,y));
                }else{
                    player_2_moves.push_back(pair<int,int>(x,y));
                }

                if(this_is_movement_number==1 && swap_rule && !(who_starts==1 && vs_robot==true)){
                    cout<<"\n>>>> Player "<<(player%2)+1<<", do you want to use SWAP (y/n)?"<<endl;
                    bool wanna_swap;
                    string auxswp;
                    cin>>auxswp;
                    if(auxswp=="y" || auxswp=="Y" || auxswp=="yes" || auxswp=="YES" || auxswp=="Yes"){
                        wanna_swap = true;
                        cout<<">> Player "<<(player%2)+1<<" is using SWAP.\n"<<endl;
                    }else if(auxswp=="n" || auxswp=="N" || auxswp=="no" || auxswp=="NO" || auxswp=="No"){
                        wanna_swap = false;
                        cout<<">> Player "<<(player%2)+1<<" is NOT using SWAP.\n"<<endl;
                    }else{
                        wanna_swap = false;
                        cout<<"-- Invalid input. Player "<<(player%2)+1<<" is NOT using SWAP.\n"<<endl;
                    }

                    if(wanna_swap){
                        swap_has_been_done = true;
                        if(player==1){
                            player_1_moves.clear();
                            player_2_moves.push_back(pair<int,int>(x,y));
                            board.set_node_tag_byCoordinates(x,y,2);
                        }else{
                            player_2_moves.clear();
                            player_1_moves.push_back(pair<int,int>(x,y));
                            board.set_node_tag_byCoordinates(x,y,1);
                        }

                        board.draw_board_ASCII(false);
                    }
                }
                    
                // Now check if the player has won!:
                if(player==1){
                    game_finished = check_connection_vertical();
                    if(game_finished){
                        who_won = 1;
                    }
                }else{
                    game_finished = check_connection_lateral();
                    if(game_finished){
                        who_won = 2;
                    }
                }

                ++this_is_movement_number;
                return;
            }

            bool check_bot_won(Hex_Board &_board){ // Special "check_connection_lateral" method, for the bot's implementation
                // Check if there is a path between any of the nodes of the West border and
                // any of the nodes of the East border, considering only nodes of player 2 ("O")
                // and using Dijkstra's shortest path algorithm
                bool connects = false;
                ShortestPath<Hex_Board, int> path(_board);
                vector<int> avoid_these_tags;
                avoid_these_tags.push_back(0);
                avoid_these_tags.push_back(1);
                for(int w=0; w<_board.get_border_length(); ++w){
                    for(int e=0; e<_board.get_border_length(); ++e){
                        int nodeFrom = _board.coordinate_to_nodeIndex(w,0);
                        int nodeTo = _board.coordinate_to_nodeIndex(e,_board.get_border_length()-1);
                        path.seek_path(nodeFrom, nodeTo, avoid_these_tags);
                        if(path.get_path_exists()){
                            connects = true;
                            break;
                        }
                    }
                    if(connects){
                        break;
                    }
                }
                return connects;
            }

            bool check_connection_vertical(){
                // Check if there is a path between any of the nodes of the North border and
                // any of the nodes of the South border, considering only nodes of player 1 ("X")
                // and using Dijkstra's shortest path algorithm
                bool connects = false;
                ShortestPath<Hex_Board, int> path(board);
                vector<int> avoid_these_tags;
                avoid_these_tags.push_back(0);
                avoid_these_tags.push_back(2);
                for(int n=0; n<border_length; ++n){
                    for(int s=0; s<border_length; ++s){
                        int nodeFrom = board.coordinate_to_nodeIndex(0,n);
                        int nodeTo = board.coordinate_to_nodeIndex(border_length-1,s);
                        path.seek_path(nodeFrom, nodeTo, avoid_these_tags);
                        if(path.get_path_exists()){
                            connects = true;
                            break;
                        }
                    }
                    if(connects){
                        break;
                    }
                }
                return connects;
            }

            bool check_connection_lateral(){
                // Check if there is a path between any of the nodes of the West border and
                // any of the nodes of the East border, considering only nodes of player 2 ("O")
                // and using Dijkstra's shortest path algorithm
                bool connects = false;
                ShortestPath<Hex_Board, int> path(board);
                vector<int> avoid_these_tags;
                avoid_these_tags.push_back(0);
                avoid_these_tags.push_back(1);
                for(int w=0; w<border_length; ++w){
                    for(int e=0; e<border_length; ++e){
                        int nodeFrom = board.coordinate_to_nodeIndex(w,0);
                        int nodeTo = board.coordinate_to_nodeIndex(e,border_length-1);
                        path.seek_path(nodeFrom, nodeTo, avoid_these_tags);
                        if(path.get_path_exists()){
                            connects = true;
                            break;
                        }
                    }
                    if(connects){
                        break;
                    }
                }
                return connects;
            }

            void game_loop(){ // This is the loop which runs the game.

                board.draw_board_ASCII(false);
                
                if(vs_robot){
                    int current_player = who_starts;
                    while(!game_finished){
                        if(current_player==1){
                            if(this_is_movement_number==2 && swap_rule){
                                cout<<"\n>>>> Player 1, do you want to use SWAP (y/n)?"<<endl;
                                bool wanna_swap;
                                string auxswp;
                                cin>>auxswp;
                                if(auxswp=="y" || auxswp=="Y" || auxswp=="yes" || auxswp=="YES" || auxswp=="Yes"){
                                    wanna_swap = true;
                                    cout<<">> Player 1 is using SWAP.\n"<<endl;
                                }else if(auxswp=="n" || auxswp=="N" || auxswp=="no" || auxswp=="NO" || auxswp=="No"){
                                    wanna_swap = false;
                                    cout<<">> Player 1 is NOT using SWAP.\n"<<endl;
                                }else{
                                    wanna_swap = false;
                                    cout<<"-- Invalid input. Player 1 is NOT using SWAP.\n"<<endl;
                                }

                                if(wanna_swap){
                                    swap_has_been_done = true;
                                    int x = player_2_moves[0].first;
                                    int y = player_2_moves[0].second;
                                    player_2_moves.clear();
                                    player_1_moves.push_back(pair<int,int>(x,y));
                                    board.set_node_tag_byCoordinates(x,y,1);

                                    ++this_is_movement_number;
                                    
                                    board.draw_board_ASCII(false);
                                }
                            }else{player_move_by_input(current_player);}
                            
                            current_player = (current_player%2)+1;

                        }else{
                            cout<<"\n>>>> Robot player 2 is choosing its move. Please wait...\n...\n..."<<endl;

                            // Check what nodes haven't been already played
                            vector<int> unused_nodes;
                            vector<int> shufflable;
                            for(int i=0; i<board.V(); ++i){
                                if(board.get_node_tag(i)==0){
                                    unused_nodes.push_back(i);
                                    shufflable.push_back(i);
                                }
                            }
                                                
                            // Now, for each possible movement, run the Monte Carlo computation
                            vector<pair<int, double>> nodes_and_ratios;
                            for(auto fixed_possible_node : unused_nodes){
                                int bot_victories = 0;
                                int human_victories = 0;
                                double ratio_bot_victories = 0;
                                for(int it = 0; it<N_MC_ITERATIONS; ++it){
                                    int aux_current_player = 2; // (initialize to 2, it's the robot's move)
                                    Hex_Board* aux_board = new Hex_Board(this->board); // Copy-constructed
                                    aux_board->set_node_tag(fixed_possible_node, aux_current_player); // Mark the fixed move on the auxiliary board
                                    shuffle(begin(shufflable), end(shufflable), randengine); // Shuffle the vector in a random order
                                    
                                    int aux_this_is_movement_number = this_is_movement_number;
                                    if(swap_rule){ // Possibility of swap
                                        int aux_index = 0;
                                        int nodes_examined = 0;
                                        int aux_current_node = fixed_possible_node;
                                        while(nodes_examined<shufflable.size()){
                                            if(aux_this_is_movement_number==2 && aux_current_player==1 &&\
                                            probability_using_swap(gen)<0.5){ // Player 1 randomly chooses whether to do swap or not
                                                aux_board->set_node_tag(fixed_possible_node, aux_current_player);
                                                aux_current_player = (aux_current_player%2)+1;
                                            }else{
                                                aux_board->set_node_tag(aux_current_node, aux_current_player);
                                                aux_current_player = (aux_current_player%2)+1;
                                                ++nodes_examined;
                                                if(shufflable[aux_index] != fixed_possible_node){
                                                    aux_current_node = shufflable[aux_index];
                                                    ++aux_index;
                                                }else{
                                                    if(aux_index+1<shufflable.size()){
                                                        aux_current_node = shufflable[aux_index+1];
                                                        aux_index+=2;
                                                    }
                                                }
                                            }
                                            ++aux_this_is_movement_number;
                                        }
                                    }else{ // No swap permitted
                                        for(auto next_node : shufflable){
                                            if(next_node != fixed_possible_node){
                                                aux_board->set_node_tag(next_node, aux_current_player);
                                                aux_current_player = (aux_current_player%2)+1;
                                                ++aux_this_is_movement_number;
                                            }
                                        }
                                    }
                                    // Check who won this Monte Carlo iteration:
                                    if(check_bot_won(*aux_board)){ // Player 2 (bot) wins
                                        ++bot_victories;
                                    }else{ // DON'T CHECK THE CONNECTION AGAIN, BECAUSE IF PLAYER 2 HAS LOST, PLAYER 1 HAS WON!
                                        ++human_victories;
                                    }
                                    delete aux_board; // As we have used a pointer, the aux board can be deleted after each Monte Carlo step
                                    // and therefore we have a clean variable for the next iteration
                                }
                                ratio_bot_victories = static_cast<double>(bot_victories)/(bot_victories+human_victories);
                                
                                // Save the results of Monte Carlo runs for this fixed_possible_node:
                                nodes_and_ratios.push_back(pair<int,double>(fixed_possible_node,ratio_bot_victories));
                            }

                            // Now, if the swap rule can be used, examine that special case:
                            double ratio_bot_victories_with_swap = -1;
                            int index_for_swap_rule = -999;
                            int player1_first_move = -999;
                            if(this_is_movement_number==2 && swap_rule){
                                player1_first_move = board.coordinate_to_nodeIndex(player_1_moves[player_1_moves.size()-1].first,\
                                player_1_moves[player_1_moves.size()-1].second);
                                int bot_victories = 0;
                                int human_victories = 0;
                                for(int it = 0; it<N_MC_ITERATIONS; ++it){
                                    int aux_current_player = 2; // (initialize to 2, it's the robot's move)
                                    Hex_Board* aux_board = new Hex_Board(this->board); // Copy-constructed
                                    aux_board->set_node_tag(player1_first_move, aux_current_player); // Undoing the Player 1's first move and marking
                                    // it as Player 2's !
                                    aux_current_player = (aux_current_player%2)+1; // After the swap, return the turn to the Player 1
                                    shuffle(begin(shufflable), end(shufflable), randengine); // Shuffle the vector in a random order
                                    for(auto next_node : shufflable){
                                        if(next_node != player1_first_move){
                                            aux_board->set_node_tag(next_node, aux_current_player);
                                            aux_current_player = (aux_current_player%2)+1;
                                        }
                                    }
                                    // Check who won this Monte Carlo iteration:
                                    if(check_bot_won(*aux_board)){ // Player 2 (bot) wins
                                        ++bot_victories;
                                    }else{ // DON'T CHECK THE CONNECTION AGAIN, BECAUSE IF PLAYER 2 HAS LOST, PLAYER 1 HAS WON!
                                        ++human_victories;
                                    }
                                    delete aux_board; // As we have used a pointer, the aux board can be deleted after each Monte Carlo step
                                    // and therefore we have a clean variable for the next iteration
                                }
                                ratio_bot_victories_with_swap = static_cast<double>(bot_victories)/(bot_victories+human_victories);
                            }
                            
                            // Examine all of the possible nodes, choose the most favorable one and mark it as the bot's move:
                            int temp_index_of_max = nodes_and_ratios[0].first;
                            double temp_max = nodes_and_ratios[0].second;
                            if(nodes_and_ratios.size()>1){
                                for(int i = 1; i<nodes_and_ratios.size();++i){
                                    if(nodes_and_ratios[i].second>temp_max){
                                        temp_index_of_max = nodes_and_ratios[i].first;
                                        temp_max = nodes_and_ratios[i].second;
                                    }
                                }
                            }

                            // If swap rule is permitted and is benefitial, use it:
                            if(swap_rule && ratio_bot_victories_with_swap>temp_max){
                                temp_max = ratio_bot_victories_with_swap;
                                temp_index_of_max = player1_first_move;

                                board.set_node_tag(temp_index_of_max, 2); // Undo the Player 1's first movement and mark it as Player 2's
                                player_2_moves.push_back(pair<int,int>(board.nodeIndex_to_coordinate(temp_index_of_max).first,\
                                board.nodeIndex_to_coordinate(temp_index_of_max).second));
                                player_1_moves.pop_back(); // Delete it from the record of player 1's moves

                                // Now, pass the turn to player 1
                                current_player = (current_player%2)+1;

                                // No need to check win condition now. It's just second movement.

                                swap_has_been_done = true;
                                cout<<"\n>>>> Bot Player 2 has used SWAP RULE and captured Player 1's first move.\n"<<endl;

                            }else{ // Swap rule hasn't been used
                                board.set_node_tag(temp_index_of_max, 2);
                                player_2_moves.push_back(pair<int,int>(board.nodeIndex_to_coordinate(temp_index_of_max).first,\
                                board.nodeIndex_to_coordinate(temp_index_of_max).second));

                                // Now, pass the turn to player 1
                                current_player = (current_player%2)+1;

                                // Now check if the player 2 (bot) has won. If so, mark the game as terminated:
                                game_finished = check_connection_lateral();
                                if(game_finished){who_won = 2;}

                                cout<<"\n>>>> Player 2 has chosen the square (x, y) = ("<<\
                                board.nodeIndex_to_coordinate(temp_index_of_max).first<<\
                                ", "<<board.nodeIndex_to_coordinate(temp_index_of_max).second<<").\n"<<endl;
                            }

                            // Update the moves counter:
                            ++this_is_movement_number;

                            board.draw_board_ASCII(false);
                        }
                    }
                    if(who_won==1){
                        cout<<"\n* - * - * - * - * - * - * - * - * -"<<endl;
                        cout<<"Congratulations PLAYER "<<who_won<<". You win!"<<endl;
                        cout<<"* - * - * - * - * - * - * - * - * -"<<endl;
                    }else{
                        cout<<"\n* - * - * - * - * - * - * - * - * -"<<endl;
                        cout<<"ROBOT PLAYER 2 wins!\nMaybe next time, Player 1..."<<endl;
                        cout<<"* - * - * - * - * - * - * - * - * -"<<endl;
                    }

                }else{
                    int current_player = who_starts;
                    player_move_by_input(current_player);
                    if(swap_has_been_done){
                        current_player = who_starts;
                    }else{
                        current_player = (current_player%2)+1;
                    }
                    while(!game_finished){
                        player_move_by_input(current_player);
                        current_player = (current_player%2)+1;
                    }
                    cout<<"\n* - * - * - * - * - * - * - * - * -"<<endl;
                    cout<<"Congratulations PLAYER "<<who_won<<". You win!"<<endl;
                    cout<<"* - * - * - * - * - * - * - * - * -"<<endl;
                }

                cout<<"\nEnd of game. Press E + ENTER to exit."<<endl;
                string _aux;
                cin>>_aux;
                return;
            }

        // Class members:
        // ==============
        private:
            Hex_Board board;
            int border_length;
            vector<pair<int, int>> player_1_moves;
            vector<pair<int, int>> player_2_moves;
            int who_starts; // Indicates whether player 1 or player 2 will do the first move
            bool vs_robot; // If true, player 2 will be the computer. If false, both players will be humans
            bool swap_rule; // If true, the second player to move will have the option to take over the first
            // player's first move
            int this_is_movement_number; // Indicates the number of the current movement of the game (starting at 1)
            bool swap_has_been_done; // Indicates whether the second player to move has chosen to use the swap rule
            bool game_finished;
            int who_won;
    };
}

// ==================================================================================================
// main
// ==================================================================================================
int main(){

    // This version of the program permits playing against the computer.
    // But if so, do not use a board greater than 7x7, or the computation will be too slow!
    cout<<"Implementation of Hex game. An intelligent bot opponent has been added"<<endl;
    cout<<"so you can play against the computer."<<endl;

    // To play Hex with this program, the user only has to create an object Graph::Hex_Game,
    // initialize it (by providing all of the arguments to the constructor, or by providing only
    // the size of the board and then using the terminal prompts to initialize the game.)
    // Then, just call the method game_loop() and the game will progress.

    int border_length;
    cout<<"\n\n>>>>Initializing Hex Game. First choose the size (the border length) of the board."<<endl;
    cout<<">>>>Which size would you like for the board? (please enter an integer number greater than 2)"<<endl;
    cout<<"\n    (NOTICE. If you want to play versus computer, choose a board NOT GREATER than 7 !!"<<endl;
    cout<<"    Otherwise the computation would be too slow!)\n>>Choose the size now"<<endl;
    cin>>border_length;

    // Creating the game object:
    Graph::Hex_Game game(border_length); // Settings will be requested via terminal prompts
    // Graph::Hex_Game game(border_length,1,false,true); // (Providing settings
    // // via constructor (border_length, who_starts, vs_robot, swap_rule) )

    // Initiating the game loop:
    game.game_loop();

    // Game has finished.
    cout<<"Program will exit now."<<endl;
    
    return 0;
}
