package z3.scala

import jnr.ffi.Pointer

sealed class Z3Pattern private[z3](val ptr: Pointer, val context: Z3Context) extends Z3ASTLike {
  override def toString : String = context.patternToString(this)

  locally {
    context.astQueue.track(this)
  }
}
