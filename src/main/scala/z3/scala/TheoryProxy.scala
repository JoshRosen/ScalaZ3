package z3.scala

import jnr.ffi.Pointer
import z3.AbstractTheoryProxy

/** This class serves as a router for calls from Z3 to the Scala <code>Z3Theory</code> 
 * instances. Instances of <code>TheoryProxy</code> are automatically created and should not
 * be managed by the user. Their methods should not be called manually. */
sealed class TheoryProxy private[z3](context: Z3Context, thy: Z3Theory) extends AbstractTheoryProxy {
  private var sc: Boolean = false
  private var sp: String = ""

  final def showCalls(show: Boolean, prefix: String) : Unit = {
    sc = show
    sp = prefix
  }

  private def msg(name: String, args: Any*) : Unit = if(sc) {
    if(args.isEmpty) {
      println("In theory " + sp + ": " + name + " was called.")
    } else {
      println("In theory " + sp + ": " + name + " was called with args :")
      println(args.toSeq.toList.mkString("  ", ",\n  ", ""))
    }
  }

  def delete(tPtr: Pointer) : Unit = {
    msg("delete")
    thy.delete
  }
  def reduceEq(tPtr: Pointer, t1: Pointer, t2: Pointer, out: Pointer) : Boolean = {
    val a1 = new Z3AST(t1, context)
    val a2 = new Z3AST(t2, context)
    msg("reduceEq", a1, a2)
    thy.reduceEq(a1, a2) match {
      // TODO(josh) case Some(ast) => out.set = ast.ptr; true
      case None => false
    } 
  }
  def reduceApp(tPtr: Pointer, fdPtr: Pointer, argc: Int, args: Array[Pointer], out: Pointer) : Boolean = {
    val fd = new Z3FuncDecl(fdPtr, Z3Wrapper.getDomainSize(context.ptr, fdPtr), context);
    val aa = args.map(new Z3AST(_, context)) 
    msg("reduceApp", (fd +: aa) : _*)
    thy.reduceApp(fd, aa : _*) match {
      // TODO(josh) case Some(ast) => out.ptr = ast.ptr; true
      case None => false
    }
  }
  def reduceDistinct(tPtr: Pointer, argc: Int, args: Array[Pointer], out: Pointer) : Boolean = {
    val aa = args.map(new Z3AST(_, context))
    msg("reduceDistinct", aa : _*)
    thy.reduceDistinct(aa : _*) match {
      // TODO(josh) case Some(ast) => out.ptr = ast.ptr; true
      case None => false
    }
  }
  def newApp(tPtr: Pointer, appPtr: Pointer) : Unit = {
    val a = new Z3AST(appPtr, context)
    msg("newApp", a)
    thy.newApp(a)
  }
  def newElem(tPtr: Pointer, elemPtr: Pointer) : Unit = {
    val a = new Z3AST(elemPtr, context)
    msg("newElem", a)
    thy.newElem(a)
  }
  def initSearch(tPtr: Pointer) : Unit = {
    msg("initSearch")
    thy.initSearch
  }
  def push(tPtr: Pointer) : Unit = {
    msg("push")
    thy.push
  }
  def pop(tPtr: Pointer) : Unit = {
    msg("pop")
    thy.pop
  }
  def restart(tPtr: Pointer) : Unit = {
    msg("restart")
    thy.restart
  }
  def reset(tPtr: Pointer) : Unit = {
    msg("reset")
    thy.reset
  }
  def finalCheck(tPtr: Pointer) : Boolean = {
    msg("finalCheck")
    thy.finalCheck
  }
  def newEq(tPtr: Pointer, t1: Pointer, t2: Pointer) : Unit = {
    val a1 = new Z3AST(t1, context)
    val a2 = new Z3AST(t2, context)
    msg("newEq", a1, a2)
    thy.newEq(a1, a2)
  }
  def newDiseq(tPtr: Pointer, t1: Pointer, t2: Pointer) : Unit = {
    val a1 = new Z3AST(t1, context)
    val a2 = new Z3AST(t2, context)
    msg("newDiseq", a1, a2)
    thy.newDiseq(a1, a2)
  }
  def newAssignment(tPtr: Pointer, pred: Pointer, polarity: Boolean) : Unit = {
    val a = new Z3AST(pred, context)
    msg("newAssignment", a, polarity)
    thy.newAssignment(a, polarity)
  }
  def newRelevant(tPtr: Pointer, t: Pointer) : Unit = {
    val a = new Z3AST(t, context)
    msg("newRelevant", a)
    thy.newRelevant(a)
  }
}
