import simplifier._

Simplifier.parseCompare[Int]("==", 3 ,4 )
Simplifier.parseCompare[Int]("==", 4 ,4 )
Simplifier.parseCompare[Int]("<", 3 ,4 )
Simplifier.parseCompare[Int]("<", 5 ,-10 )
Simplifier.parseCompare[Int]("<=", 5 ,5 )
Simplifier.parseCompare[Int]("<=", 3 ,5 )
Simplifier.parseCompare[Int](">", 3 ,7 )
Simplifier.parseCompare[Int](">", 6 ,2 )
Simplifier.parseCompare[Int](">=", 5 ,5 )
Simplifier.parseCompare[Int](">=", 21 ,5 )


Simplifier.parseCompare[Double]("==", 2.0 ,4.0 )
Simplifier.parseCompare[Double]("==", 4.3 ,4.5 )
Simplifier.parseCompare[Double]("<", 3.1 ,4.6 )
Simplifier.parseCompare[Double]("<", 5.2 ,-10.12 )
Simplifier.parseCompare[Double]("<=", 5.3 ,5.3 )
Simplifier.parseCompare[Double]("<=", 3.3 ,5.7 )
Simplifier.parseCompare[Double](">", 3.1 ,7.1 )
Simplifier.parseCompare[Double](">", 6.5 ,2.3 )
Simplifier.parseCompare[Double](">=", 5.4 ,5.2 )
Simplifier.parseCompare[Double](">=", 21.5 ,5.6 )