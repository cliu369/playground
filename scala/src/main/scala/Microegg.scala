// https://pavpanchekha.com/blog/microegg.html
import scala.collection.mutable.{ArrayBuffer, HashMap}

object Microegg: 
  type ID = Int

  case class Node(val f: String, val l: List[ID])

  object Leaf:
    def apply(name: String): Node = Node(name, Nil)

  class UnionFind:
    val parent: ArrayBuffer[ID] = ArrayBuffer[ID]()

    def makeset: ID = 
      val new_id = parent.length
      parent.append(new_id)
      new_id

    def find(id: ID): ID = 
      if parent(id) == id then id else find(parent(id))

    def union(a : ID, b: ID): Boolean = 
      val pa = find(a)
      val pb = find(b)
      if pa == pb then false else 
        parent.update(pb, pa) 
        true

    def are_equal(a: ID, b: ID): Boolean = 
      find(a) == find(b)
  end UnionFind

  def testUF() = 
    val test_uf = UnionFind()
    val (a, b, c) = (test_uf.makeset, test_uf.makeset, test_uf.makeset)
    test_uf.union(a, b)
    test_uf.union(b, c)
    assert(test_uf.are_equal(a, c))

  enum Pattern:
    case Var(name: String)
    case App(f: String, l: List[Pattern])

  type Substitution = HashMap[String, ID]

  case class Rewrite(lhs: Pattern, rhs: Pattern)
  case class Match(rhs: Pattern, root: ID, subst: Substitution)

  class EGraph: 
    import Pattern.*
    val union_find: UnionFind = UnionFind()
    val memo: HashMap[Node, ID] = HashMap[Node, ID]()

    def is_equiv(a : ID, b: ID): Boolean = 
      union_find.are_equal(a, b)

    def canonicalize_node(n: Node): Node = 
      Node(n.f, n.l.map(union_find.find))

    def add(node: Node): ID =  
      val n = canonicalize_node(node)
      memo.get(n) match
        case Some(id) => id
        case None => 
          val new_id = union_find.makeset
          memo(n) = new_id
          new_id
    
    def union(a: ID, b: ID): Boolean = 
      union_find.union(a, b)

    def rebuild: Unit = 
      var keep_going = true
      while keep_going do
        keep_going = false
        val old_memo = memo.clone()
        memo.clear()

        for (old_node, old_id) <- old_memo do
          val new_node = canonicalize_node(old_node)
          val new_id = memo.get(new_node) match
            case Some(id) => id
            case None => 
              val new_id = union_find.find(old_id)
              memo(new_node) = new_id
              new_id
          if union(new_id, old_id) then keep_going = true
    
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
          case Some(bound_id) =>
            if bound_id == root then 
              ArrayBuffer[Substitution](subst)
            else ArrayBuffer[Substitution]()
         
        case App(f, subpats) =>
          val nodes = nodes_in_classes(root).filterInPlace(node => 
            node.f == f && node.l.length == subpats.length
          )
          val outputs = ArrayBuffer[Substitution]()
          for node <- nodes do 
            var todo = List(subst)
            for (sub_id, sub_pat) <- node.l.zip(subpats) do
              todo = todo.flatMap(new_subst => 
                ematch_rec(sub_pat, sub_id, new_subst)
              )
            outputs.appendAll(todo)
          outputs 
    end ematch_rec    
        
    def ematch(pat: Pattern, root: ID): ArrayBuffer[Substitution] =
      ematch_rec(pat, root, HashMap[String, ID]())

    def all_ids: Set[ID] = memo.values.toSet

    def rewrite(rules: List[Rewrite]): Unit = 
      val matches = ArrayBuffer[Match]() 
      for 
        rule <- rules  
        id <- all_ids 
      do 
        val substs = ematch(rule.lhs, id)
        for subst <- substs do
          matches.append(Match(rule.rhs, id, subst))

      for match_obj <- matches do
        val new_id = instantiate(match_obj.rhs, match_obj.subst)
        union(match_obj.root, new_id) 

    def saturate(rules: List[Rewrite]): Unit = 
      rebuild
      var fingerprint = (union_find.parent.length, memo.size)
      var nofixpoint = true
      while nofixpoint do
        rewrite(rules)
        rebuild
        val new_fingerprint = (union_find.parent.length, memo.size)
        if fingerprint == new_fingerprint then
          nofixpoint = false
        else 
          fingerprint = new_fingerprint

  end EGraph 

  def testEG1() = 
    val test_eg = EGraph()
    val (a, a_copy, b) = (Leaf("a"), Leaf("a"), Leaf("b"))
    val (a_id, a_copy_id, b_id) = (test_eg.add(a), test_eg.add(a_copy), test_eg.add(b))
    assert(a_id == a_copy_id)
    assert(a_id != b_id)
  
  def testEG2() = 
    val test_eg = EGraph()
    val (a, b) = (Leaf("a"), Leaf("b"))
    val (a_id, b_id) = (test_eg.add(a), test_eg.add(b))
    val f_a = Node("f", a_id :: Nil)
    val f_b = Node("f", b_id :: Nil)
    val (f_a_id, f_b_id) = (test_eg.add(f_a), test_eg.add(f_b))
    test_eg.union(a_id, b_id)
    test_eg.rebuild
    assert(test_eg.is_equiv(f_a_id, f_b_id))

  def testEG3() = 
    import Pattern.*
    val test_eg = EGraph()
    val root = test_eg.instantiate(
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
    test_eg.saturate(rules) 
    println(test_eg.all_ids.size)
    println(test_eg.memo.size)

  def run(): Unit =
    testEG3()
  
end Microegg
