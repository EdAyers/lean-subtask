## Human-oriented term rewiting.

__Subtask__ is a new approach to proof planning developed by Edward Ayers, Tim Gowers and Mateja Jamnik at the University of Cambridge.

# Summary of algorithm

We maintain a DAG of _tasks_ and _strategies_ called the __task graph__.
We maintain a list of _strategies_ called the __front__.

We update the state by doing one of two things:
Find a 



# [TODO] 

- [ ] generate lookahead from all equality lemmas tagged with -- eg `@[subgoal]` or perhaps just all lemmas
- [ ] write refiners for tasks and strategies
    + [ ] find smallest uncommon subterms
    + [ ] write code to traverse 'proper terms' which are expressions that are not types/instances and not partially applied terms.
- [ ] bring over the graph code
- [ ] write some code that finds all possible state updates.
- [ ] measure the 'entropy' of a state. 
