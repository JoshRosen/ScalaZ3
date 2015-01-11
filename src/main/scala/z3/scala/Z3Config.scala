package z3.scala

import jnr.ffi.Pointer

sealed class Z3Config(params: (String,Any)*) {
  val ptr: Pointer = Z3Wrapper.Z3_mk_config()

  for((k,v) <- params) {
    Z3Wrapper.setParamValue(this.ptr, k, v.toString)
  }

  def delete() : Unit = {
    Z3Wrapper.delConfig(this.ptr)
  }

  def setParamValue(paramID: String, paramValue: String) : Z3Config = {
    Z3Wrapper.setParamValue(this.ptr, paramID, paramValue)
    this
  }
}
