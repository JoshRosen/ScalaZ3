package z3.scala

import jnr.ffi.Pointer

sealed class Z3Symbol private[z3](val ptr: Pointer, context: Z3Context) extends Z3Pointer {
  override def equals(that: Any) : Boolean = {
    that != null && that.isInstanceOf[Z3Symbol] && that.asInstanceOf[Z3Symbol].ptr == this.ptr
  }

  def getKind : Z3SymbolKind[_] = context.getSymbolKind(this)

  private lazy val strRepr: String = getKind match {
    case Z3IntSymbol(v) => "sym#" + v
    case Z3StringSymbol(s) => s
  }
  override def toString : String = strRepr
}
