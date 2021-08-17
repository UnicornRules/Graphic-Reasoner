This code is a work in progress on a way to use the Hypergraphical Approach in order to create an OWL EL+ reasoner.

The code isn't making much use of the workspace at the moment, i wanted to take some distance from the object oriented programming in order to be able to implement multiprocessing in a more simple manner.

5 function for  5 rules : 

function 1 : H1
function 2 : H2 with B1, B2
function 3 : H2 with B1, r
function 4 : H3 with A1, r
function 5:  H2 with A1, A2, s


The code compare  direct_subsumption.H2A with processed_pool.H2A
                 and processed_pool.H2A and unfold processed_pool.H2A  in order to check wether the code is correct.
                
Need to understand why 1/10 times , one axiom is missing 
Need to add multiprocessing
Need to test with galen7 / snomed but i don't really understand how to use those subsumptions.
