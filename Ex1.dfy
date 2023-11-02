datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
  decreases t 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

// Ex 1

function deserialise<V>(cs : seq<Code<V>>) : seq<Tree<V>>
{
  deserialiseAux(cs, [])
}

function deserialiseAux<V>(cs : seq<Code<V>>, t : seq<Tree<V>>) : seq<Tree<V>>
  decreases cs, t 
{
  if (cs == []) 
    then t
  else deserialiseAux(cs[1..], convert(cs[0], t))
}

function convert<V>(c : Code<V>, t : seq<Tree<V>>) : seq<Tree<V>>
{
  match c {
    case CLf(v) => [ Leaf(v) ] + t
    case CSNd(v) => 
      if (|t| < 1) then [] 
      else [SingleNode(v, t[0])] + t[1..]
    case CDNd(v) => 
      if (|t| < 2) then []
      else [DoubleNode(v, t[0], t[1])] + t[2..]
  }
}

// Ex 2

method testSerialise1()
{
  var t := SingleNode(1, Leaf(2));
  var cs := serialise(t);
  assert cs == [CLf(2), CSNd(1)];
}

method testSerialise2()
{
  var t := Leaf(1);
  var cs := serialise(t);
  assert cs == [CLf(1)];
}

method testSerialise3()
{
  var t := DoubleNode(1, Leaf(2), Leaf(3));
  var cs := serialise(t);
  assert cs == [CLf(3), CLf(2), CDNd(1)];
}

// Ex 3 

method testDeserialise1()
{
  var cs := [CLf(5), CSNd(2)];
  var t := deserialise(cs);
  assert t == [SingleNode(2, Leaf(5))];
}

method testDeserialise2()
{
  var cs := [CLf(1)];
  var t := deserialise(cs);
  assert t == [Leaf(1)];
}

method testDeserialise3()
{
  var cs := [CLf(3), CLf(2), CDNd(1)];
  var t := deserialise(cs);
  assert t == [DoubleNode(1, Leaf(2), Leaf(3))];
}

// Ex 4 

lemma SerialiseLemma<V> (t : Tree<V>) 
  ensures deserialise(serialise(t)) == [t] 
{
  calc {
      deserialise(serialise(t));
      == { assert serialise(t) == serialise(t) + [];}
      deserialiseAux(serialise(t) + [], []);
      == { SerialiseLemmaAux(t, [], []); }
      deserialiseAux([], [t] + []);
      ==     
      deserialiseAux([], [t] + []);
      == 
      deserialiseAux([], [t]); 
      == 
      [t];
  }
} 


lemma SerialiseLemmaAux<V>(t : Tree<V>, cds : seq<Code<V>>, ts : seq<Tree<V>>)
  ensures deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, [t] + ts)
  decreases t 
{
  match t {

    case Leaf(x) => 
      calc == {
        deserialiseAux(serialise(t) + cds, ts);
        ==
        deserialiseAux(serialise(Leaf(x)) + cds, ts);
        ==
        deserialiseAux([CLf(x)] + cds, ts);
        ==
        deserialiseAux(cds, convert(CLf(x), ts));
        ==
        deserialiseAux(cds, [Leaf(x)] + ts);
      }

    case SingleNode(x, y) =>
      assert serialise(y) + [CSNd(x)] + cds == serialise(y) + ([CSNd(x)] + cds); 
      calc == {
        deserialiseAux(serialise(SingleNode(x, y))+ cds, ts);
        == 
        deserialiseAux(serialise(y) + [CSNd(x)] + cds, ts);
        ==
        deserialiseAux(serialise(y) + ([CSNd(x)] + cds), ts);
        == 
        deserialiseAux([CSNd(x)] + cds, [y] + ts);
        == { SerialiseLemmaAux(y, [CSNd(x)] + cds, ts); }
        deserialiseAux(cds, convert(CSNd(x), [y] + ts));
        == 
        deserialiseAux(cds, [SingleNode(x, y)] + ts);
        ==
        deserialiseAux(cds, [t] + ts);
      }

    case DoubleNode(x, y, z) =>
      assert serialise(z) + serialise(y) + [CDNd(x)] + cds == serialise(z) + (serialise(y) + [CDNd(x)] + cds);
      assert serialise(z) + [CDNd(x)] + cds == serialise(z) + ([CDNd(x)] + cds); 
      assert  [y] + ([z] + ts) == [y, z] + ts;
      calc == {
        deserialiseAux(serialise(DoubleNode(x, y, z)) + cds, ts);
        ==
        deserialiseAux(serialise(z) + serialise(y) + [CDNd(x)] + cds, ts);
        ==
        deserialiseAux(serialise(z) + (serialise(y) + [CDNd(x)] + cds), ts);
        == { SerialiseLemmaAux(z, serialise(y) + [CDNd(x)] + cds, ts);}
        deserialiseAux(serialise(y) + [CDNd(x)] + cds, [z] + ts);
        == { assert serialise(y) + [CDNd(x)] + cds == serialise(y) + ([CDNd(x)] + cds);}
        deserialiseAux(serialise(y) + ([CDNd(x)] + cds), [z] + ts);
        == { SerialiseLemmaAux(y, [CDNd(x)] + cds, [z] + ts); }
        deserialiseAux([CDNd(x)] + cds, [y] + [z] + ts);
        == 
        deserialiseAux(cds, convert(CDNd(x), [y, z] + ts));
        == 
        deserialiseAux(cds, [DoubleNode(x, y, z)] + ts);
      }
  }
}
