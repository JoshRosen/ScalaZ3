package z3.scala

import jnr.ffi.Pointer

class Z3Tactic private[z3](val ptr : Pointer, val context : Z3Context) extends Z3Object {
  override def equals(that : Any) : Boolean = {
    that != null &&
      that.isInstanceOf[Z3Tactic] && {
      val that2 = that.asInstanceOf[Z3Tactic]
      that2.ptr == this.ptr // && context.isEqAST(this, that2)
    }
  }

  def incRef() {
    Z3Wrapper.Z3_tactic_inc_ref(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.Z3_tactic_dec_ref(context.ptr, this.ptr)
  }

  locally {
    context.tacticQueue.track(this)
  }
}
