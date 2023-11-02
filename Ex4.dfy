include "Ex3.dfy"


module Ex4 {


import Ex3=Ex3

class Queue {

  var lst1 : Ex3.Node?
  var lst2 : Ex3.Node? 

  ghost var footprint : set<Ex3.Node>
  ghost var list : seq<int>

  // Ex1
  
  ghost function Valid() : bool 
    reads this, footprint, lst1, lst2
    reads if(lst1 != null) then lst1.footprint else {}, if(lst2 != null) then lst2.footprint else {}
    decreases footprint
  {
    if (lst1 == null && lst2 == null) 
      then footprint == {} && list == []
    else if (lst1 != null && lst2 == null)
      then lst1.Valid() && footprint == lst1.footprint && list == lst1.list 
    else if (lst1 == null && lst2 != null)
      then lst2.Valid() && footprint == lst2.footprint && list == lst2.list
    else 
      lst1.Valid() && lst2.Valid() 
      && footprint == lst1.footprint + lst2.footprint 
      && list == lst1.list + lst2.list 
      && lst1.footprint !! lst2.footprint
  }

  // Ex2 

  constructor () 
    ensures Valid() 
      && lst1 == null 
      && lst2 == null
      && footprint == {}
      && list == []
  {
    this.lst1 := null; 
    this.lst2 := null;  
    this.footprint := {};
    this.list := [];
  } 

  // Ex3.1

  method push(val : int) 
    requires Valid()
    ensures Valid()
    modifies this
    ensures lst1 != null
    ensures old(lst1) != null ==> fresh(lst1.footprint - old(lst1.footprint))
    ensures list == [val] + old(list)
    ensures footprint == {lst1} + old(footprint)
  {
    lst1 := Ex3.ExtendList(lst1, val);
    
    footprint := {lst1} + footprint;
    list := [val] + list;
  }

  // Ex3.2

  method pop() returns (r : int)
    requires Valid()
    ensures Valid()
    requires lst1 != null || lst2 != null
    requires |list| > 0 && footprint != {}
    modifies this, footprint, lst1, lst2
    modifies if(lst1 != null) then lst1.footprint else {}, if(lst2 != null) then lst2.footprint else {} 
    ensures old(lst2) == null ==> lst1 == null
    ensures old(lst2) == null && old(lst1) != null && lst2 != null ==> lst2.list == Ex3.rev(old(lst1.list))[1..]
  {
    if (lst2 == null) {
      lst2 := lst1.reverse(null); 
      lst1 := null;
    }

    r := lst2.data; 
    lst2 := lst2.next; 

    if (lst1 == null && lst2 == null) {footprint := {}; list := [];}
    else if (lst1 != null && lst2 == null) {footprint := lst1.footprint; list := lst1.list;}
    else if (lst1 == null && lst2 != null) {footprint := lst2.footprint; list := lst2.list;}
    else {footprint := lst1.footprint + lst2.footprint; list := lst1.list + lst2.list;}

    return;
    
  }
  
}

}

