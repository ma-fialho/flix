///////////////////////////////////////////////////////////////////////////////
/// Unit                                                                    ///
///////////////////////////////////////////////////////////////////////////////
rel UnitRel(x: Unit)

@test
def testUnitCapturedVar01(): Bool =
    let c = ();
    let x = UnitRel(c).;
    let y = UnitRel(c) :- UnitRel(c).;
    let r = solve x <+> y;
    r |= UnitRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Bool                                                                    ///
///////////////////////////////////////////////////////////////////////////////
rel BoolRel(x: Bool)

@test
def testBoolCapturedVar01(): Bool =
    let c = true;
    let x = BoolRel(c).;
    let y = BoolRel(c) :- BoolRel(c).;
    let r = solve x <+> y;
    r |= BoolRel(c).

@test
def testBoolCapturedVar02(): Bool =
    let c = false;
    let x = BoolRel(c).;
    let y = BoolRel(c) :- BoolRel(c).;
    let r = solve x <+> y;
    r |= BoolRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Char                                                                    ///
///////////////////////////////////////////////////////////////////////////////
rel CharRel(x: Char)

@test
def testCharCapturedVar01(): Bool =
    let c = ' ';
    let x = CharRel(c).;
    let y = CharRel(c) :- CharRel(c).;
    let r = solve x <+> y;
    r |= CharRel(c).

@test
def testCharCapturedVar02(): Bool =
    let c = 'a';
    let x = CharRel(c).;
    let y = CharRel(c) :- CharRel(c).;
    let r = solve x <+> y;
    r |= CharRel(c).

@test
def testCharCapturedVar03(): Bool =
    let c = 'x';
    let x = CharRel(c).;
    let y = CharRel(c) :- CharRel(c).;
    let r = solve x <+> y;
    r |= CharRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Float32                                                                 ///
///////////////////////////////////////////////////////////////////////////////
rel Float32Rel(x: Float32)

@test
def testFloat32CapturedVar01(): Bool =
    let c = 0.0f32;
    let x = Float32Rel(c).;
    let y = Float32Rel(c) :- Float32Rel(c).;
    let r = solve x <+> y;
    r |= Float32Rel(c).

@test
def testFloat32CapturedVar02(): Bool =
    let c = 123.456f32;
    let x = Float32Rel(c).;
    let y = Float32Rel(c) :- Float32Rel(c).;
    let r = solve x <+> y;
    r |= Float32Rel(c).

@test
def testFloat32CapturedVar03(): Bool =
    let c = -123.456f32;
    let x = Float32Rel(c).;
    let y = Float32Rel(c) :- Float32Rel(c).;
    let r = solve x <+> y;
    r |= Float32Rel(c).

///////////////////////////////////////////////////////////////////////////////
/// Float64                                                                 ///
///////////////////////////////////////////////////////////////////////////////
rel Float64Rel(x: Float64)

@test
def testFloat64CapturedVar01(): Bool =
    let c = 0.0f64;
    let x = Float64Rel(c).;
    let y = Float64Rel(c) :- Float64Rel(c).;
    let r = solve x <+> y;
    r |= Float64Rel(c).

@test
def testFloat64CapturedVar02(): Bool =
    let c = 123.456f64;
    let x = Float64Rel(c).;
    let y = Float64Rel(c) :- Float64Rel(c).;
    let r = solve x <+> y;
    r |= Float64Rel(c).

@test
def testFloat64CapturedVar03(): Bool =
    let c = -123.456f64;
    let x = Float64Rel(c).;
    let y = Float64Rel(c) :- Float64Rel(c).;
    let r = solve x <+> y;
    r |= Float64Rel(c).

///////////////////////////////////////////////////////////////////////////////
/// Int8                                                                    ///
///////////////////////////////////////////////////////////////////////////////
rel Int8Rel(x: Int8)

@test
def testInt8CapturedVar01(): Bool =
    let c = 0i8;
    let x = Int8Rel(c).;
    let y = Int8Rel(c) :- Int8Rel(c).;
    let r = solve x <+> y;
    r |= Int8Rel(c).

@test
def testInt8CapturedVar02(): Bool =
    let c = 123i8;
    let x = Int8Rel(c).;
    let y = Int8Rel(c) :- Int8Rel(c).;
    let r = solve x <+> y;
    r |= Int8Rel(c).

@test
def testInt8CapturedVar03(): Bool =
    let c = -123i8;
    let x = Int8Rel(c).;
    let y = Int8Rel(c) :- Int8Rel(c).;
    let r = solve x <+> y;
    r |= Int8Rel(c).

///////////////////////////////////////////////////////////////////////////////
/// Int16                                                                   ///
///////////////////////////////////////////////////////////////////////////////
rel Int16Rel(x: Int16)

@test
def testInt16CapturedVar01(): Bool =
    let c = 0i16;
    let x = Int16Rel(c).;
    let y = Int16Rel(c) :- Int16Rel(c).;
    let r = solve x <+> y;
    r |= Int16Rel(c).

@test
def testInt16CapturedVar02(): Bool =
    let c = 123i16;
    let x = Int16Rel(c).;
    let y = Int16Rel(c) :- Int16Rel(c).;
    let r = solve x <+> y;
    r |= Int16Rel(c).

@test
def testInt16CapturedVar03(): Bool =
    let c = -123i16;
    let x = Int16Rel(c).;
    let y = Int16Rel(c) :- Int16Rel(c).;
    let r = solve x <+> y;
    r |= Int16Rel(c).

///////////////////////////////////////////////////////////////////////////////
/// Int32                                                                   ///
///////////////////////////////////////////////////////////////////////////////
rel Int32Rel(x: Int32)

@test
def testInt32CapturedVar01(): Bool =
    let c = 0i32;
    let x = Int32Rel(c).;
    let y = Int32Rel(c) :- Int32Rel(c).;
    let r = solve x <+> y;
    r |= Int32Rel(c).

@test
def testInt32CapturedVar02(): Bool =
    let c = 123i32;
    let x = Int32Rel(c).;
    let y = Int32Rel(c) :- Int32Rel(c).;
    let r = solve x <+> y;
    r |= Int32Rel(c).

@test
def testInt32CapturedVar03(): Bool =
    let c = -123i32;
    let x = Int32Rel(c).;
    let y = Int32Rel(c) :- Int32Rel(c).;
    let r = solve x <+> y;
    r |= Int32Rel(c).

///////////////////////////////////////////////////////////////////////////////
/// Int64                                                                   ///
///////////////////////////////////////////////////////////////////////////////
rel Int64Rel(x: Int64)

@test
def testInt64CapturedVar01(): Bool =
    let c = 0i64;
    let x = Int64Rel(c).;
    let y = Int64Rel(c) :- Int64Rel(c).;
    let r = solve x <+> y;
    r |= Int64Rel(c).

@test
def testInt64CapturedVar02(): Bool =
    let c = 123i64;
    let x = Int64Rel(c).;
    let y = Int64Rel(c) :- Int64Rel(c).;
    let r = solve x <+> y;
    r |= Int64Rel(c).

@test
def testInt64CapturedVar03(): Bool =
    let c = -123i64;
    let x = Int64Rel(c).;
    let y = Int64Rel(c) :- Int64Rel(c).;
    let r = solve x <+> y;
    r |= Int64Rel(c).

///////////////////////////////////////////////////////////////////////////////
/// BigInt                                                                  ///
///////////////////////////////////////////////////////////////////////////////
rel BigIntRel(x: BigInt)

@test
def testBigIntCapturedVar01(): Bool =
    let c = 0ii;
    let x = BigIntRel(c).;
    let y = BigIntRel(c) :- BigIntRel(c).;
    let r = solve x <+> y;
    r |= BigIntRel(c).

@test
def testBigIntCapturedVar02(): Bool =
    let c = 123ii;
    let x = BigIntRel(c).;
    let y = BigIntRel(c) :- BigIntRel(c).;
    let r = solve x <+> y;
    r |= BigIntRel(c).

@test
def testBigIntCapturedVar03(): Bool =
    let c = -123ii;
    let x = BigIntRel(c).;
    let y = BigIntRel(c) :- BigIntRel(c).;
    let r = solve x <+> y;
    r |= BigIntRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Str                                                                     ///
///////////////////////////////////////////////////////////////////////////////
rel StrRel(x: Str)

@test
def testStrCapturedVar01(): Bool =
    let c = "";
    let x = StrRel(c).;
    let y = StrRel(c) :- StrRel(c).;
    let r = solve x <+> y;
    r |= StrRel(c).

@test
def testStrCapturedVar02(): Bool =
    let c = "hello";
    let x = StrRel(c).;
    let y = StrRel(c) :- StrRel(c).;
    let r = solve x <+> y;
    r |= StrRel(c).

@test
def testStrCapturedVar03(): Bool =
    let c = "hello world!";
    let x = StrRel(c).;
    let y = StrRel(c) :- StrRel(c).;
    let r = solve x <+> y;
    r |= StrRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Option                                                                  ///
///////////////////////////////////////////////////////////////////////////////
rel OptionRel(x: Option[Int])

@test
def testOptionCapturedVar01(): Bool =
    let c = None;
    let x = OptionRel(c).;
    let y = OptionRel(c) :- OptionRel(c).;
    let r = solve x <+> y;
    r |= OptionRel(c).

@test
def testOptionCapturedVar02(): Bool =
    let c = Some(123);
    let x = OptionRel(c).;
    let y = OptionRel(c) :- OptionRel(c).;
    let r = solve x <+> y;
    r |= OptionRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Result                                                                  ///
///////////////////////////////////////////////////////////////////////////////
rel ResultRel(x: Result[Int, Str])

@test
def testResultCapturedVar01(): Bool =
    let c = Ok(123);
    let x = ResultRel(c).;
    let y = ResultRel(c) :- ResultRel(c).;
    let r = solve x <+> y;
    r |= ResultRel(c).

@test
def testResultCapturedVar02(): Bool =
    let c = Err("goodbye world!");
    let x = ResultRel(c).;
    let y = ResultRel(c) :- ResultRel(c).;
    let r = solve x <+> y;
    r |= ResultRel(c).

///////////////////////////////////////////////////////////////////////////////
/// Tuple                                                                   ///
///////////////////////////////////////////////////////////////////////////////
rel TupleRel(x: (Bool, Char, Int))

@test
def testTupleCapturedVar01(): Bool =
    let c = (true, 'a', 42);
    let x = TupleRel(c).;
    let y = TupleRel(c) :- TupleRel(c).;
    let r = solve x <+> y;
    r |= TupleRel(c).

@test
def testTupleCapturedVar02(): Bool =
    let c = (false, 'x', -42);
    let x = TupleRel(c).;
    let y = TupleRel(c) :- TupleRel(c).;
    let r = solve x <+> y;
    r |= TupleRel(c).
