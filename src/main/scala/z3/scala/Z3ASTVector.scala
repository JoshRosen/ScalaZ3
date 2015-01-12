package z3.scala

import jnr.ffi.Pointer

final class Z3ASTVector private[z3](val ptr : Pointer, val context : Z3Context) extends Z3Object {

  def incRef() {
    Z3Wrapper.Z3_ast_vector_inc_ref(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.Z3_ast_vector_dec_ref(context.ptr, this.ptr)
  }

  def get(i: Int): Z3AST = {
    new Z3AST(Z3Wrapper.Z3_ast_vector_get(context.ptr, this.ptr, i), context)
  }

  def set(i: Int, v: Z3AST) {
    Z3Wrapper.Z3_ast_vector_set(context.ptr, this.ptr, i, v.ptr)
  }

  def size: Int = {
    Z3Wrapper.Z3_ast_vector_size(context.ptr, this.ptr)
  }

  // Utility functions
  def apply(i: Int): Z3AST = {
    get(i)
  }

  def update(i: Int, v: Z3AST) = {
    set(i, v)
  }

  def toSeq: Seq[Z3AST] = {
    for (i <- 0 until size) yield {
      get(i)
    }
  }

  locally {
    context.astvectorQueue.track(this)
  }
}
