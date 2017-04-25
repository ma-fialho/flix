namespace TestImplicits {

    namespace Test01 {
        rel A(x: Int, implicit b: Bool)
        rel R(x: Int, implicit b: Bool)

        A(21, true).
        A(42, false).

        R(x) :- A(x).           // equivalent to R(x, b) :- A(x, b).
    }

    namespace Test02 {
        rel A(x: Int, implicit b: Bool)
        rel R(x: Int, implicit b: Bool)

        A(21, true).
        A(42, false).

        R(x, b) :- A(x, b).     // direct style, no implicits
    }

    namespace Test03 {
        rel A(x: Int, y: Int, implicit b: Bool)
        rel R(x: Int, implicit b: Bool)

        A(21, 21, true).
        A(42, 42, false).

        R(x) :- A(x, 21).       // equivalent to R(x, b) :- A(x, 21, b).
    }

    namespace Test03 {
        rel A(x: Int, implicit b: Bool)
        rel B(x: Int, implicit b: Bool)
        rel R(x: Int)

        A(21, 21, true).
        A(42, 42, false).
        B(21, 21, true).

        R(x) :- A(x), B(x).     // equivalent to R(x) :- A(x, b), B(x, b).
    }


}