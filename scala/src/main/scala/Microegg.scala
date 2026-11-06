// https://pavpanchekha.com/blog/microegg.html
package Microegg
import scala.collection.mutable.{ArrayBuffer, HashMap}

type ID = Int

case class Node(val f: String, val l: List[ID])

object Leaf:
  def apply(name: String): Node = Node(name, Nil)

class UnionFind:
  val parent: ArrayBuffer[ID] = ArrayBuffer[ID]()

  def makeset: ID = 
    val newId = parent.length
    parent.append(newId)
    newId

  def find(id: ID): ID = 
    if parent(id) == id then id else find(parent(id))

  /**
    * @return true if a change was made to UF, false otherwise.
    */
  def union(a : ID, b: ID): Boolean = 
    val pa = find(a)
    val pb = find(b)
    if pa == pb then false else 
      parent.update(pb, pa) 
      true

  def equiv(a: ID, b: ID): Boolean = 
    find(a) == find(b)
end UnionFind

enum Pattern:
  case Var(name: String)
  case App(f: String, l: List[Pattern])
import Pattern.*

type Substitution = HashMap[String, ID]

case class Rewrite(lhs: Pattern, rhs: Pattern)
case class Match(rhs: Pattern, root: ID, subst: Substitution)

class EGraph: 
  val uf: UnionFind = UnionFind()
  val memo: HashMap[Node, ID] = HashMap[Node, ID]()

  def equiv(a : ID, b: ID): Boolean = 
    uf.equiv(a, b)

  def canonicalize_node(n: Node): Node = 
    Node(n.f, n.l.map(uf.find))

  def add(node: Node): ID =  
    val n = canonicalize_node(node)
    memo.get(n) match
      case Some(id) => id
      case None => 
        val newId = uf.makeset
        memo(n) = newId
        newId
  
  def union(a: ID, b: ID): Boolean = 
    uf.union(a, b)
    
  def rebuild: Unit = 
    var keep_going = true
    while keep_going do
      keep_going = false
      val old_memo = memo.clone()
      memo.clear()

      for (old_node, old_id) <- old_memo do
        val new_node = canonicalize_node(old_node)
        val newId = memo.get(new_node) match
          case Some(id) => id
          case None => 
            val newId = uf.find(old_id)
            memo(new_node) = newId
            newId
        if union(newId, old_id) then keep_going = true
  end rebuild
  
  def instantiate(pat: Pattern, subst: Substitution): ID = 
    pat match
      case Var(name) => subst(name)
      case App(f, l) => 
        val node = Node(f, l.map(instantiate(_, subst)))
        add(node) 

  def nodes_in_classes(root: ID): ArrayBuffer[Node] = 
    val out = ArrayBuffer[Node]() 
    for (node, id) <- memo do
      if id == root then out.append(node)
    out

  def ematch_rec(pat: Pattern, root: ID, subst: Substitution): ArrayBuffer[Substitution] = 
    pat match
      case Var(name) => subst.get(name) match
        case None =>
          val new_subst = subst.clone()
          new_subst(name) = root
          ArrayBuffer[Substitution](new_subst)
        case Some(boundId) =>
          if boundId == root then 
            ArrayBuffer[Substitution](subst)
          else ArrayBuffer[Substitution]()
        
      case App(f, subpats) =>
        val nodes = nodes_in_classes(root).filterInPlace(node => 
          node.f == f && node.l.length == subpats.length
        )
        val outputs = ArrayBuffer[Substitution]()
        for node <- nodes do 
          var todo = List(subst)
          for (subId, subpat) <- node.l.zip(subpats) do
            todo = todo.flatMap(new_subst => 
              ematch_rec(subpat, subId, new_subst)
            )
          outputs.appendAll(todo)
        outputs 
  end ematch_rec    
      
  def ematch(pat: Pattern, root: ID): ArrayBuffer[Substitution] =
    ematch_rec(pat, root, HashMap[String, ID]())

  def allIds: Set[ID] = memo.values.toSet

  def rewrite(rules: List[Rewrite]): Unit = 
    val matches = ArrayBuffer[Match]() 
    for 
      rule <- rules  
      id <- allIds
    do 
      val substs = ematch(rule.lhs, id)
      for subst <- substs do
        matches.append(Match(rule.rhs, id, subst))

    for match_obj <- matches do
      val newId = instantiate(match_obj.rhs, match_obj.subst)
      union(match_obj.root, newId) 
  end rewrite

  def saturate(rules: List[Rewrite]): Unit = 
    rebuild
    var fingerprint = (uf.parent.length, memo.size)
    var nofixpoint = true
    while nofixpoint do
      rewrite(rules)
      rebuild
      val new_fingerprint = (uf.parent.length, memo.size)
      if fingerprint == new_fingerprint then
        nofixpoint = false
      else 
        fingerprint = new_fingerprint
  end saturate
end EGraph 

object Microegg:
  def testUF() = 
    val uf = UnionFind()
    val (a, b, c) = (uf.makeset, uf.makeset, uf.makeset)
    uf.union(a, b)
    uf.union(b, c)
    assert(uf.equiv(a, c))  

  def testEG1() = 
    val egg = EGraph()
    val (a, a_copy, b) = (Leaf("a"), Leaf("a"), Leaf("b"))
    val (a_id, a_copy_id, b_id) = (egg.add(a), egg.add(a_copy), egg.add(b))
    assert(a_id == a_copy_id)
    assert(a_id != b_id)
  
  def testEG2() = 
    val egg = EGraph()
    val (a, b) = (Leaf("a"), Leaf("b"))
    val (a_id, b_id) = (egg.add(a), egg.add(b))
    val f_a = Node("f", a_id :: Nil)
    val f_b = Node("f", b_id :: Nil)
    val (f_a_id, f_b_id) = (egg.add(f_a), egg.add(f_b))
    egg.union(a_id, b_id)
    egg.rebuild
    assert(egg.equiv(f_a_id, f_b_id))

  def testEG3() = 
    val egg = EGraph()
    val root = egg.instantiate(
    App("+", List(
        App("+", List(
            App("+", List(
                App("a", List()),
                App("b", List()),
            )),
            App("+", List(
                App("c", List()),
                App("d", List()),
            )),
        )),
        App("+", List(
            App("+", List(
                App("e", List()),
                App("f", List()),
            )),
            App("g", List()),
        )),
    )),
    HashMap[String, ID]())
    val rules = List(
      Rewrite(App("+", List(Var("a"), Var("b"))), App("+", List(Var("b"), Var("a")))),
      Rewrite(
        App("+", List(App("+", List(Var("a"), Var("b"))), Var("c"))), 
        App("+", List(Var("a"), App("+", List(Var("b"), Var("c"))))))
    )
    egg.saturate(rules) 
    println(egg.allIds.size)
    println(egg.memo.size)

  def run(): Unit =
    testEG3()
      
end Microegg
