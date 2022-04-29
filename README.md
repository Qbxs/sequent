# Sequent calculus

Automatic proof search in the style of Gentzen's sequent calculus LK for propostional logic.

For example
~~~console
sequent "(p&q->r)->p->q->r" 
~~~

yields the following derivation in LK:
~~~
  axiom      axiom             
 ——————     ——————             
p,q ⊢ p,r  p,q ⊢ q,r    axiom  
————————————————— ∧r   ——————  
     p,q ⊢ p∧q,r      p,q,r ⊢ r
———————————————————————————— →l
         p∧q→r,p,q ⊢ r         
———————————————————————————— →r
         p∧q→r,p ⊢ q→r         
———————————————————————————— →r
         p∧q→r ⊢ p→q→r         
———————————————————————————— →r
        ⊢ (p∧q→r)→p→q→r   
~~~

Also implements a sat solver for a formula in clause form very loosely based on LK.

Usage with `stack` installed:
```console
stack run sequent <clauses>
```
or for proof search in LK:
```console
stack run sequent <formula>
```

*In case there are any problems while parsing, put the argument between ""*

Alternatively you can install the executable on the path with
```console
stack install sequent
```

Design of the SAT-solver:
- based on a single sided LK-calculus (all formulae are on the left hand side)
- the conjunction-left rule is not being used, all clauses are immediately pushed individually on the left hand side of the sequent
- instead of axiom, we check whether the literals on the left hand side of the sequent are resolvable (which would be equivalent to a contradiction in the antecedens)
- Once a satisfying interpretation is found (using dfs) the sat-solver stops