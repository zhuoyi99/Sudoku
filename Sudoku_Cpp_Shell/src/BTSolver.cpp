#include"BTSolver.hpp"
#include<climits>
using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	return network.isConsistent();
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
    //failed when check consistent
    if(network.isConsistent() == false)
    {
	    return make_pair(map<Variable*, Domain>(), false);
    }
    std::map<Variable*, Domain>result;

    // find the variable attempted  assgiend 
    for(Variable* v : network.getVariables())
    {
        if(v->isAssigned() == true)
        {
            int valueAssigned = v->getAssignment();
            //update neighbours's domain
	        ConstraintNetwork::VariableSet neighbours = network.getNeighborsOfVariable(v);
            for(Variable* nei : neighbours)
            {
                //skip the variable that assigned already
                if(nei->isAssigned() == true)
                {
                    continue;
                }

                //skip it if this neighbour doesn't contains v's value
                if(nei->getDomain().contains(valueAssigned) == false)
                {
                    continue;
                }

                //track the neighbour's domain
                trail->push(nei);
                Domain domain = nei->getDomain();
                domain.remove(valueAssigned);
                nei->setDomain(domain);
                result[nei] = domain;
            }
        }	
    }
    return make_pair(result, true);
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
    //failed when check consistent
    if(network.isConsistent() == false)
    {
	    return make_pair(map<Variable*, int>(), false);
    }

    //do prune,   search for the variable  assgiend already
    for(Variable* v : network.getVariables())
    {
        if(v->isAssigned() == true)
        {
            int valueAssigned = v->getAssignment();
            //update neighbours's domain
	        ConstraintNetwork::VariableSet neighbours = network.getNeighborsOfVariable(v);
            for(Variable* nei : neighbours)
            {
                //skip the variable that assigned already
                if(nei->isAssigned() == true)
                {
                    continue;
                }

                //skip it if this neighbour doesn't contains v's value
                if(nei->getDomain().contains(valueAssigned) == false)
                {
                    continue;
                }

                //track the neighbour's domain
                trail->push(nei);
                Domain domain = nei->getDomain();
                domain.remove(valueAssigned);
                nei->setDomain(domain);
            }
        }	
    }

    //do norvig check below
    map<Variable*, int>variableChanged;
    std::vector<Constraint>constraintSet = network.getConstraints();

    bool updated = true;
    while(updated)
    {
        updated = false;
        for(Constraint constraint:constraintSet)
        {
            std::map<int, int>valueCount;
            for(Variable* var:constraint.vars)
            {
                //skip the variable that assigned already
                if(var->isAssigned() == true)
                {
                    continue;
                }

                for(int value:var->getDomain().getValues())
                {
                    valueCount[value] += 1;
                }
            }
            
            //the value which count only one
            int valueThatCountOne = -1;

            // iterator values
            for(auto it=valueCount.begin(); it!=valueCount.end(); ++it)
            {
                if(it->second == 1)
                {
                    updated = true;
                    valueThatCountOne = it->first;
                    break;       
                }
            }

            //need to assign a variable
            if(updated == true)
            {
                for(Variable* var:constraint.vars)
                {
                    //skip the variable that assigned already
                    if(var->isAssigned() == true)
                    {
                        continue;
                    }

                    if(var->getDomain().contains(valueThatCountOne))
                    {
                        trail->push(var);
                        variableChanged[var] = valueThatCountOne;
                        var->assignValue(valueThatCountOne);
                        break;
                    }
                }
                break;
            }
        }
    }
    
    return make_pair(variableChanged, true);
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
   return norvigCheck().second;
    
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
    int minimumRemainingValue = INT_MAX;
    Variable* result = nullptr;
    std::vector<Variable*>variableSet = network.getVariables();
    //iterator all variable:
    for(Variable* var : variableSet)
    {    
        //skip the assigned variable
        if(var->isAssigned() == true)
        {
            continue;
        }

        //variable that has fewer-remaining-value found
        if(var->size() < minimumRemainingValue)
        {
            minimumRemainingValue = var->size();
            result = var;
        }
    } 
    return result;
}



/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
    int minimumRemainingValue = INT_MAX;
    vector<Variable*> result;
    std::vector<Variable*>variableSet = network.getVariables();
    //iterator all variable:
    for(Variable* var : variableSet)
    {
        //skip the assigned variable
        if(var->isAssigned() == true)
        {
            continue;
        }

        //variable that has fewer-remaining-value found
        if(var->size() < minimumRemainingValue)
        {
            minimumRemainingValue = var->size();
            result.clear();
            result.push_back(var);
        }
        else if(var->size() == minimumRemainingValue)
        {   
            result.push_back(var);
        }
    }

    //check whther success
    if(result.size() == 0)
    {
        result.push_back(nullptr);
        return result;
    }

    std::map<Variable*, int>countOfUnsignedNeighbour;
    for(int i = 0; i < result.size(); ++i)
    {
        int count = 0;
	    ConstraintNetwork::VariableSet neighbours = network.getNeighborsOfVariable(result[i]);
        for(Variable* nei : neighbours)
        {
            if(nei->isAssigned() == false)
            {
                count += 1;
            }
        }
        countOfUnsignedNeighbour[result[i]] = count;
    }

    //sort the variable by the number of unsigned neighbours
    std::sort(result.begin(), result.end(), [countOfUnsignedNeighbour](Variable* v1, Variable* v2){return countOfUnsignedNeighbour.at(v1) > countOfUnsignedNeighbour.at(v2);});
    return result;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
    return MRVwithTieBreaker( ).front();

      

}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
    Domain domain = v->getDomain();
    vector<Variable*>neighbors=network.getNeighborsOfVariable(v);
    std::map<int, int>countOfKnockedOut;
    for(int value:domain.getValues())
    {
        countOfKnockedOut[value] = 0;
    }

    for(int value:domain.getValues())
    {
      
        for(Variable* nei : neighbors)
        {
            //skip the variable that assigned already
            //if(nei->isAssigned() == true)
            //{
             //   continue;
            //}

            Domain domainOfNei = nei->getDomain();
            if(domainOfNei.contains(value))
            {
                countOfKnockedOut[value] += 1;
            }
        }
    }
    
    vector<int>valueSet = domain.getValues();
    std::sort(valueSet.begin(),valueSet.end(),[countOfKnockedOut](int a, int b){
        if(countOfKnockedOut.at(a) != countOfKnockedOut.at(b)){
            return countOfKnockedOut.at(a) < countOfKnockedOut.at(b);
        }else{
            return a < b;
        }
    });

    return valueSet;
}



/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
    return getValuesLCVOrder(v);
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
