package z3.scala

import jnr.ffi.Pointer
import jnr.ffi.byref.{IntByReference, PointerByReference}

object Z3Model {
  implicit def ast2int(model: Z3Model, ast: Z3AST): Option[Int] = {
    val res = model.eval(ast)
    if (res.isEmpty)
      None
    else
      model.context.getNumeralInt(res.get).value
  }

  implicit def ast2bool(model: Z3Model, ast: Z3AST): Option[Boolean] = {
    val res = model.eval(ast)
    if (res.isEmpty)
      None
    else
      model.context.getBoolValue(res.get)
  }

  implicit def ast2intSet(model: Z3Model, ast: Z3AST) : Option[Set[Int]] = model.eval(ast) match {
    case None => None
    case Some(evaluated) => model.getSetValue(evaluated) match {
      case Some(astSet) =>
        Some(astSet.map(elem => model.evalAs[Int](elem)).foldLeft(Set[Int]())((acc, e) => e match {
          case Some(value) => acc + value
          case None => acc
        }))
      case None => None
    }
  }
}

sealed class Z3Model private[z3](val ptr: Pointer, val context: Z3Context) extends Z3Object {
  override def toString : String = context.modelToString(this)

  @deprecated("Z3Model.delete() not be used, use incref/decref instead", "")
  def delete: Unit = {
  }

  def incRef() {
    Z3Wrapper.Z3_model_inc_ref(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.Z3_model_dec_ref(context.ptr, this.ptr)
  }

  def eval(ast: Z3AST, completion: Boolean = false) : Option[Z3AST] = {
    if (this.ptr.address() == 0L) {
      throw new IllegalStateException("The model is not initialized.")
    }
    val newAstPtr = new PointerByReference()
    val result = Z3Wrapper.Z3_model_eval(context.ptr, this.ptr, ast.ptr, completion, newAstPtr)
    if (result) {
      Some(new Z3AST(newAstPtr.getValue, context))
    } else {
      None
    }
  }

  def evalAs[T](input: Z3AST)(implicit converter: (Z3Model, Z3AST) => Option[T]): Option[T] = {
    converter(this, input)
  }

  def getModelConstants: Iterator[Z3FuncDecl] = {
    val model = this
    new Iterator[Z3FuncDecl] {
      val total: Int = Z3Wrapper.Z3_get_model_num_constants(context.ptr, model.ptr)
      var returned: Int = 0

      override def hasNext: Boolean = (returned < total)
      override def next(): Z3FuncDecl = {
        val toReturn = new Z3FuncDecl(Z3Wrapper.Z3_get_model_constant(context.ptr, model.ptr, returned), 0, context)
        returned += 1
        toReturn
      }
    }
  }

  def getModelConstantInterpretations : Iterator[(Z3FuncDecl, Z3AST)] = {
    val model = this
    val constantIterator = getModelConstants
    new Iterator[(Z3FuncDecl, Z3AST)] {
      override def hasNext: Boolean = constantIterator.hasNext
      override def next(): (Z3FuncDecl, Z3AST) = {
        val nextConstant = constantIterator.next()
        (nextConstant, model.eval(nextConstant()).get)
      }
    }
  }

  private lazy val constantInterpretationMap: Map[String, Z3AST] =
   getModelConstantInterpretations.map(p => (p._1.getName.toString, p._2)).toMap

  def getModelConstantInterpretation(name: String): Option[Z3AST] =
    constantInterpretationMap.get(name) match {
      case None => None
      case Some(v) => Some(v.asInstanceOf[Z3AST])
    }

  def getModelFuncInterpretations : Iterator[(Z3FuncDecl, Seq[(Seq[Z3AST], Z3AST)], Z3AST)] = {
    val model = this
    new Iterator[(Z3FuncDecl, List[(List[Z3AST], Z3AST)], Z3AST)] {
      val total: Int = Z3Wrapper.Z3_get_model_num_funcs(context.ptr, model.ptr)
      var returned: Int = 0

      override def hasNext: Boolean = (returned < total)
      override def next(): (Z3FuncDecl, List[(List[Z3AST], Z3AST)], Z3AST) = {
        val declPtr = Z3Wrapper.Z3_get_model_func_decl(context.ptr, model.ptr, returned)
        val arity = Z3Wrapper.Z3_get_domain_size(context.ptr, declPtr)
        val funcDecl = new Z3FuncDecl(declPtr, arity, context)
        val numEntries = Z3Wrapper.Z3_get_model_func_num_entries(context.ptr, model.ptr, returned)
        val entries = for (entryIndex <- 0 until numEntries) yield {
          val numArgs = Z3Wrapper.Z3_get_model_func_entry_num_args(context.ptr, model.ptr, returned, entryIndex)
          val arguments = for (argIndex <- 0 until numArgs) yield {
            new Z3AST(Z3Wrapper.Z3_get_model_func_entry_arg(context.ptr, model.ptr, returned, entryIndex, argIndex), context)
          }
          (arguments.toList, new Z3AST(Z3Wrapper.Z3_get_model_func_entry_value(context.ptr, model.ptr, returned, entryIndex), context))
        }
        val elseValue = new Z3AST(Z3Wrapper.Z3_get_model_func_else(context.ptr, model.ptr, returned), context)
        returned += 1
        (funcDecl, entries.toList, elseValue)
      }
    }
  }

  private lazy val funcInterpretationMap: Map[Z3FuncDecl, (Seq[(Seq[Z3AST], Z3AST)], Z3AST)] =
    getModelFuncInterpretations.map(i => (i._1, (i._2, i._3))).toMap

  def isArrayValue(ast: Z3AST) : Option[Int] = {
    val numEntriesPtr = new IntByReference()
    val result = Z3Wrapper.Z3_is_array_value(context.ptr, this.ptr, ast.ptr, numEntriesPtr)
    if (result) {
      Some(numEntriesPtr.getValue)
    } else {
      None
    }
  }

  def getArrayValue(ast: Z3AST) : Option[(Map[Z3AST, Z3AST], Z3AST)] = isArrayValue(ast) match {
    case None => None
    case Some(numEntries) =>
      val indArray = new Array[Pointer](numEntries)
      val valArray = new Array[Pointer](numEntries)
      val elseValuePtr = runtime.getMemoryManager.allocate(4)

      Z3Wrapper.Z3_get_array_value(context.ptr, this.ptr, ast.ptr, numEntries, indArray, valArray, elseValuePtr)

      val elseValue = new Z3AST(elseValuePtr, context)
      val map = Map((indArray.map(new Z3AST(_, context)) zip valArray.map(new Z3AST(_, context))): _*)
      Some((map, elseValue))
  }

  def getSetValue(ast: Z3AST) : Option[Set[Z3AST]] = this.getArrayValue(ast) match {
    case None => None
    case Some((map, elseValue)) =>
      Some(map.filter(pair => context.getBoolValue(pair._2) == Some(true)).keySet.toSet)
  }

  /* FOR VERSIONS 2.X WHERE 15 <= X <= 19 */
  def getArrayValueOld(ast: Z3AST) : Option[(Map[Z3AST, Z3AST], Z3AST)] = context.getASTKind(ast) match {
    case Z3AppAST(decl, args) => funcInterpretationMap.get(context.getDeclFuncDeclParameter(decl, 0)) match {
      case Some((entries, elseValue)) =>
        assert(entries.forall(_._1.size == 1))
        val asMap = entries.map {
          case (arg :: Nil, value) => (arg, value)
          case _ => sys.error("woot?")
        }.toMap
        Some(asMap, elseValue)
      case None => None
    }
    case _ => None
  }

  def getModelFuncInterpretation(fd: Z3FuncDecl): Option[Z3Function] = {
    funcInterpretationMap.find(i => i._1 == fd) match {
      case Some(i) => Some(new Z3Function(i._2))
      case None => None
    }
  }

  locally {
    context.modelQueue.track(this)
  }
}
