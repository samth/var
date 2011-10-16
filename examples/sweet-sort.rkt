#lang planet asumu/sweet var

define-contract list/c
  rec/c X
    or/c
      empty? 
      cons/c nat? X
  
module sorted-ne? 
  list/c → bool?
  ●
  
module sorted?
  list/c → bool?
  λ (l) 
    if empty?(l) 
       #t 
       sorted-ne?(l)    

module insert 
  nat? {list/c and/c sorted?} → {list/c and/c sorted?}
  ●

module insertion-sort
  list/c {list/c and/c sorted?} → {list/c and/c sorted?}
  λ (l acc) 
    if empty?(l)
       acc 
       insertion-sort
         rest l 
         insert(first(l) acc)

module n list/c ●
  
insertion-sort n empty
