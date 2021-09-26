# Sequent calculus

Automatic proof search in the style of Gentzen's sequent calculus LK for propostional logic.

For example
~~~
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
