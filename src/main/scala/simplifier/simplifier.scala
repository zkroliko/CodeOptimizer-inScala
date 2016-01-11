package simplifier

import math.pow
import scala.Int
import scala.collection.immutable.::
import scala.math.Ordered._

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  var variableAssignments:Map[Node,Node] = Map()

  def parseIntArithmetic(op: String, x: Int, y: Int) = op match {
    case "+" => IntNum(x+y)
    case "-" => IntNum(x-y)
    case "*" => IntNum(x*y)
    case "/" => IntNum(x/y)
    case "%" => IntNum(x%y)
    case "**" => IntNum(pow(x.toDouble, y.toDouble).toInt)
  }

  def parseDoubleArithmetic(op: String, x: Double, y: Double) = op match {
    case "+" => FloatNum(x+y)
    case "-" => FloatNum(x-y)
    case "*" => FloatNum(x*y)
    case "/" => FloatNum(x/y)
    case "%" => FloatNum(x%y)
    case "**" => FloatNum(pow(x, y))
  }

  // A bit of magic
  // https://stackoverflow.com/questions/19385235/how-to-paramaterize-int-as-ordered-in-scala
  def parseCompare[T](op: String, x: T, y: T)(implicit ordering: Ordering[T]): Node = op match {
    case "==" => if (ordering.eq(x,y)) TrueConst() else FalseConst()
    case "!=" => if (!ordering.eq(x,y)) TrueConst() else FalseConst()
    case "<" => if (ordering.lt(x,y)) TrueConst() else FalseConst()
    case "<=" => if (ordering.lteq(x,y)) TrueConst() else FalseConst()
    case ">" => if (ordering.gt(x,y))   TrueConst() else FalseConst()
    case ">=" => if (ordering.gteq(x,y))   TrueConst() else FalseConst()
  }

  def simplify(node: Node): Node = node match {

    // Concatenating lists and tuples
    case BinExpr("+", Tuple(first), Tuple(second)) => Tuple((first ++ second) map simplify)
    case BinExpr("+", ElemList(first), ElemList(second)) => ElemList((first ++ second) map simplify)

    // Removing duplicates from dictionaries
    // It associates keys of keyDatums with the whole objects,
    // then maps the resulting list to objects, leaving out duplicates
    case KeyDatumList(list) => KeyDatumList(list.foldLeft(Map.empty[Node, KeyDatum])(
      (map, keyDatum) => map + (keyDatum.key -> keyDatum)
    ).toList.map(x => x._2))

    // Removing if's with false condition
    case IfElseInstr(cond, left, right) =>
      val simplifiedCondition = simplify(cond)
      simplifiedCondition match {
        case TrueConst()  => simplify(left)
        case FalseConst() => simplify(right)
        case _            => IfElseInstr(simplifiedCondition, simplify(left), simplify(right))
      }

    case IfInstr(cond, left) =>
      val simplifiedCondition = simplify(cond)
      simplifiedCondition match {
        case TrueConst()  => simplify(left)
        case FalseConst() => DeadInstr()
        case _            => IfInstr(simplifiedCondition, simplify(left))
      }

    // Removing loops with false condition
    case WhileInstr(cond, body) =>
      val simplifiedCond = simplify(cond)
      simplifiedCond match {
        case FalseConst() => DeadInstr()
        case _ => WhileInstr(simplifiedCond, simplify(body))
      }

    // Removing assignments to itself and shortening x = y if %s else z
    // also checking for a=b; c=b using map - not in specification
    case Assignment(Variable(left), expr) => expr match {
      case Variable(y) if left == y => DeadInstr()
      case _ => expr match {
        // x = y if %s else z
        case IfElseExpr(cond,iLeft,iRight) => {
          Assignment(Variable(left),simplify(IfElseInstr(cond,iLeft,iRight)))
        }
        case Variable(right) => variableAssignments get Variable(right) match {
          case Some(Variable(original)) =>
            variableAssignments += (Variable(left) -> Variable(right) )
            //println(variableAssignments.keys)
            Assignment(Variable(left), Variable(original))
          case None => // Hasn't been assigned yet
            variableAssignments += (Variable(left) -> Variable(right) )
            //println(variableAssignments.keys)
            Assignment(Variable(left), simplify(expr))
        }
        case _ => Assignment(Variable(left), simplify(expr))
      }
    }

    // Logical simplifications

    case BinExpr(op, IntNum(x), IntNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseIntArithmetic(op,x,y)
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Integer](op,x,y)
      }

    case BinExpr(op, FloatNum(x), FloatNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseDoubleArithmetic(op,x,y)
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x,y)
      }

    case BinExpr(op, IntNum(x), FloatNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseDoubleArithmetic(op,x.doubleValue(),y)
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x.doubleValue(),y)
      }

    case BinExpr(op, FloatNum(x), IntNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseDoubleArithmetic(op,x,y.doubleValue())
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x,y.doubleValue())
      }

    case BinExpr("==", x, y) if x == y => TrueConst()
    case BinExpr("!=", x,y)  if x == y => FalseConst()
    case BinExpr(">=", x,y)  if x == y => TrueConst()
    case BinExpr("<=", x,y)  if x == y => TrueConst()
    case BinExpr("<", x,y)   if x == y => FalseConst()
    case BinExpr(">", x,y)   if x == y => FalseConst()
    case BinExpr("or", x ,y) if x == y => x
    case BinExpr("and", x,y) if x == y => x

    case BinExpr("and", left, right) =>
      (simplify(left), simplify(right)) match {
        case (_ , FalseConst()) => FalseConst()
        case (FalseConst(), _) => FalseConst()
        case (expr, TrueConst()) => expr
        case (TrueConst(), expr) => expr
        case (exprLeft, exprRight) if exprLeft == exprRight => exprLeft
        case (exprLeft, exprRight) =>
          if (exprLeft != left || exprRight != right) // Checking if it's the end of simplification
            simplify(BinExpr("and", exprLeft, exprRight))
          else BinExpr("and", exprLeft, exprRight)
      }

    case BinExpr("or", left, right) =>
      (simplify(left), simplify(right)) match {
        case (_ , TrueConst()) => TrueConst()
        case (TrueConst(), _) => TrueConst()
        case (expr, FalseConst()) => expr
        case (FalseConst(), expr) => expr
        case (exprLeft, exprRight) if exprLeft == exprRight => exprLeft
        case (exprLeft, exprRight) =>
          if (exprLeft != left || exprRight != right) // Checking if it's the end of simplification
            simplify(BinExpr("or", exprLeft, exprRight))
          else BinExpr("or", exprLeft, exprRight)
      }

    //        --- Unary expressions ---

    case Unary("not", expr) => expr match {
      case BinExpr("==", left, right) => simplify(BinExpr("!=", left, right))
      case BinExpr("!=", left, right) => simplify(BinExpr("==", left, right))
      case BinExpr("<=", left, right) => simplify(BinExpr(">",  left, right))
      case BinExpr(">=", left, right) => simplify(BinExpr("<",  left, right))
      case BinExpr("<", left, right) => simplify(BinExpr(">=", left, right))
      case BinExpr(">", left, right) => simplify(BinExpr("<=", left, right))

      case TrueConst() => FalseConst()
      case FalseConst() => TrueConst()

      case Unary("not", expr2) => simplify(expr2) // double negation

      case expr2 => Unary("not", simplify(expr2))
    }

    case Unary("-", expr) => expr match {
      case Unary("-", expr2) => simplify(expr2) // --x
      case IntNum(x)         => IntNum(-x)
      case FloatNum(x)       => FloatNum(-x)
      case expr2             => Unary("-", simplify(expr2))
    }

    //      --- Arithmetic expressions ---

    // Here a duplication for floats was required, cannot create object of generic type
    case BinExpr(op, left, right) => simplify(right) match {
      case IntNum(num) => Integer2int(num) match {
        case 0 => op match {
          case "-" | "+" => left
          case "*" => DeadInstr()
          case "/" | "%" => throw new ArithmeticException(op + " by 0")
          case "**" => IntNum(1)
          case _ => BinExpr(op, left, IntNum(num))
        }
        case 1 => op match {
          case "*" | "/" | "%" | "**" => left
          case _ => BinExpr(op, left, IntNum(num))
        }
        case _ => BinExpr(op, left, IntNum(num))
      }

      case FloatNum(num) => num match {
        case 0 => op match {
          case "-" | "+" => left
          case "*" => DeadInstr()
          case "/" | "%" => throw new ArithmeticException(op + " by 0")
          case "**" => FloatNum(1)
          case _ => BinExpr(op, left, FloatNum(num))
        }
        case 1 => op match {
          case "*" | "/" | "%" | "**" => left
          case _ => BinExpr(op, left, FloatNum(num))
        }
        case _ => BinExpr(op, left, FloatNum(num))
      }

      // Left side is equal to right side
      case `left` => op match {
        case "/" | "%" => IntNum(1)
        case "-" => IntNum(0)
        case _ => BinExpr(op, simplify(left), simplify(right))
      }

      case n => simplify(n)
    }

    // Other way around
    case BinExpr(op, left, right) => simplify(left) match {
      case IntNum(num) => Integer2int(num) match {
          case 0 => op match {
            case "-" | "+" => right
            case "*" => DeadInstr()
            case "**" => IntNum(0)
            case _ => BinExpr(op, right, IntNum(num))
          }
          case 1 => op match {
            case "*" => right
            case "**" => IntNum(1)
            case _ => BinExpr(op, right, IntNum(num))
          }
          case _ => BinExpr(op, right, IntNum(num))
        }
      case n => simplify(n)
    }

    // Other way around
    case BinExpr(op, left, right) => simplify(left) match {
      case FloatNum(num) => num match {
        case 0 => op match {
          case "-" | "+" => right
          case "*" => DeadInstr()
          case "**" => FloatNum(0)
          case _ => BinExpr(op, right, FloatNum(num))
        }
        case 1 => op match {
          case "*" => right
          case "**" => FloatNum(1)
          case _ => BinExpr(op, right, FloatNum(num))
        }
        case _ => BinExpr(op, right, FloatNum(num))
      }
      case n => simplify(n)
    }

    case Variable(name) => name match {
      case _ => Variable(name);
    }

    case KeyDatum(key,value) =>
      KeyDatum(key,simplify(value))

    case FunDef(name,args,body) =>
      FunDef(name,simplify(args),simplify(body))

    case FunCall(name,args) =>
      FunCall(name,simplify(args))

    case PrintInstr(expr) =>
      PrintInstr(simplify(expr))

    case LambdaDef(args,body) =>
      LambdaDef(simplify(args),simplify(body))

    case ClassDef(name,inh,suite) =>
      ClassDef(name,inh,simplify(suite))

    case NodeList(list) => list match {
      case Nil => DeadInstr()
      // One element list
      case (first :: Nil) => first match {
        case DeadInstr() => DeadInstr()
        case NodeList(list) => simplify(NodeList(list map simplify))
        case node =>
          val simplifiedN = simplify(node)
          if (simplifiedN != node) simplify(NodeList(List(simplify(node)))) else NodeList(List(simplifiedN))
      }
      // ----------- Peephole optimization x=a; x=b => x=b -------------

      //   TODO: Moze da sie to zrobic piekniej - 8 kombinacji

      case (Assignment(fLeft, fRight):: Assignment(left, right) :: Nil) => fLeft match {
        case left => NodeList(simplify(Assignment(fLeft, right)) :: Nil)
      }
      case (Assignment(fLeft, fRight):: Assignment(left, right) :: rest) => fLeft match {
        case left => NodeList((Assignment(fLeft, right) :: rest) map simplify)
      }
      case (Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: Nil) => fLeft match {
        case left => NodeList((middle :: Assignment(fLeft, right) :: Nil) map simplify)
      }
      case (Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: rest) => fLeft match {
        case left => NodeList((middle :: Assignment(fLeft, right) :: rest) map simplify)
      }
      case (head :: Assignment(fLeft, fRight) :: Assignment(left, right) :: Nil) => fLeft match {
        case left => NodeList((head :: Assignment(fLeft, right) :: Nil) map simplify)
      }
      case (head :: Assignment(fLeft, fRight):: Assignment(left, right) :: rest) => fLeft match {
        case left => NodeList((head :: Assignment(fLeft, right) :: rest) map simplify)
      }
      case (head :: Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: Nil) => fLeft match {
        case left => NodeList((head :: middle :: Assignment(fLeft, right) :: Nil) map simplify)
      }
      case (head :: Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: rest) => fLeft match {
        case left => NodeList((head :: middle :: Assignment(fLeft, right) :: rest) map simplify)
      }


      case _ => NodeList(list map simplify)
    }


    case ElemList(list) => ElemList(list map simplify)

    case Tuple(list) => Tuple(list map simplify)

    // Nothing can be simplified:
//    case node => StringConst(node.getClass.toString)
    case node => node;
  }
}
