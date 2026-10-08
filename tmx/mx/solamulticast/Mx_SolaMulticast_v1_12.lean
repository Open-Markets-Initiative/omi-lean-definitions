import Wire

/-!
# TMX Group Sola Multicast v1.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolamulticastHsvfV112

/-- Strike Price Fraction Indicator: one byte code -/
def StrikePriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive StrikePriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ StrikePriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrikePriceFractionIndicator

def toByte : StrikePriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrikePriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : StrikePriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrikePriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrikePriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrikePriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrikePriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrikePriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrikePriceFractionIndicator

/-- Trade Price Fraction Indicator: one byte code -/
def TradePriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive TradePriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceFractionIndicator

def toByte : TradePriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : TradePriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradePriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradePriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradePriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradePriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradePriceFractionIndicator

/-- Net Change Fraction Indicator: one byte code -/
def NetChangeFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive NetChangeFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ NetChangeFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetChangeFractionIndicator

def toByte : NetChangeFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetChangeFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : NetChangeFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetChangeFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetChangeFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetChangeFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetChangeFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NetChangeFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetChangeFractionIndicator

/-- Bid Price Fraction Indicator: one byte code -/
def BidPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive BidPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ BidPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidPriceFractionIndicator

def toByte : BidPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : BidPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BidPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidPriceFractionIndicator

/-- Ask Price Fraction Indicator: one byte code -/
def AskPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive AskPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ AskPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AskPriceFractionIndicator

def toByte : AskPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AskPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : AskPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AskPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AskPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AskPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AskPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AskPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AskPriceFractionIndicator

/-- Price Fraction Indicator: one byte code -/
def PriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive PriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceFractionIndicator

def toByte : PriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : PriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceFractionIndicator

/-- Maximum Threshold Price Fraction Indicator: one byte code -/
def MaximumThresholdPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive MaximumThresholdPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ MaximumThresholdPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceFractionIndicator

def toByte : MaximumThresholdPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MaximumThresholdPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : MaximumThresholdPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MaximumThresholdPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MaximumThresholdPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MaximumThresholdPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MaximumThresholdPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MaximumThresholdPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MaximumThresholdPriceFractionIndicator

/-- Minimum Threshold Price Fraction Indicator: one byte code -/
def MinimumThresholdPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive MinimumThresholdPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ MinimumThresholdPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceFractionIndicator

def toByte : MinimumThresholdPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MinimumThresholdPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : MinimumThresholdPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MinimumThresholdPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MinimumThresholdPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MinimumThresholdPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MinimumThresholdPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MinimumThresholdPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MinimumThresholdPriceFractionIndicator

/-- Tick Increment Fraction Indicator: one byte code -/
def TickIncrementFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive TickIncrementFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ TickIncrementFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TickIncrementFractionIndicator

def toByte : TickIncrementFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TickIncrementFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : TickIncrementFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TickIncrementFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TickIncrementFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TickIncrementFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TickIncrementFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TickIncrementFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TickIncrementFractionIndicator

/-- Tick Value Fraction Indicator: one byte code -/
def TickValueFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive TickValueFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ TickValueFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TickValueFractionIndicator

def toByte : TickValueFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TickValueFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : TickValueFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TickValueFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TickValueFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TickValueFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TickValueFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TickValueFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TickValueFractionIndicator

/-- Last Price Fraction Indicator: one byte code -/
def LastPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive LastPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ LastPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastPriceFractionIndicator

def toByte : LastPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : LastPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LastPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastPriceFractionIndicator

/-- Open Price Fraction Indicator: one byte code -/
def OpenPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive OpenPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenPriceFractionIndicator

def toByte : OpenPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : OpenPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenPriceFractionIndicator

/-- High Price Fraction Indicator: one byte code -/
def HighPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive HighPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ HighPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HighPriceFractionIndicator

def toByte : HighPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HighPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : HighPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HighPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HighPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HighPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HighPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HighPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HighPriceFractionIndicator

/-- Low Price Fraction Indicator: one byte code -/
def LowPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive LowPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ LowPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LowPriceFractionIndicator

def toByte : LowPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LowPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : LowPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LowPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LowPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LowPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LowPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LowPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LowPriceFractionIndicator

/-- Settlement Price Fraction Indicator: one byte code -/
def SettlementPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive SettlementPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementPriceFractionIndicator

def toByte : SettlementPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : SettlementPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementPriceFractionIndicator

/-- Previous Settlement Price Fraction Indicator: one byte code -/
def PreviousSettlementPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive PreviousSettlementPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ PreviousSettlementPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PreviousSettlementPriceFractionIndicator

def toByte : PreviousSettlementPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PreviousSettlementPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : PreviousSettlementPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PreviousSettlementPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PreviousSettlementPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PreviousSettlementPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PreviousSettlementPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PreviousSettlementPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PreviousSettlementPriceFractionIndicator

/-- Opening Price Fraction Indicator: one byte code -/
def OpeningPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive OpeningPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningPriceFractionIndicator

def toByte : OpeningPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : OpeningPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpeningPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningPriceFractionIndicator

/-- Previous Settlement Fraction Indicator: one byte code -/
def PreviousSettlementFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive PreviousSettlementFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ PreviousSettlementFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PreviousSettlementFractionIndicator

def toByte : PreviousSettlementFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PreviousSettlementFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : PreviousSettlementFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PreviousSettlementFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PreviousSettlementFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PreviousSettlementFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PreviousSettlementFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PreviousSettlementFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PreviousSettlementFractionIndicator

/-- External Price Fraction Indicator: one byte code -/
def ExternalPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive ExternalPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ ExternalPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExternalPriceFractionIndicator

def toByte : ExternalPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExternalPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : ExternalPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExternalPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExternalPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExternalPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExternalPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExternalPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExternalPriceFractionIndicator

/-- Min Price Fraction Indicator: one byte code -/
def MinPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive MinPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ MinPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MinPriceFractionIndicator

def toByte : MinPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MinPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : MinPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MinPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MinPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MinPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MinPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MinPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MinPriceFractionIndicator

/-- Tick Price Fraction Indicator: one byte code -/
def TickPriceFractionIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]

inductive TickPriceFractionIndicator where
  | whole -- Whole
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | negativeWhole -- Negative Whole
  | negativeTen -- Negative Ten
  | negativeHundred -- Negative Hundred
  | negativeThousand -- Negative Thousand
  | negativeTenThousand -- Negative Ten Thousand
  | negativeHundredThousand -- Negative Hundred Thousand
  | negativeMillion -- Negative Million
  | unlisted (byte : { byte : UInt8 // byte ∉ TickPriceFractionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TickPriceFractionIndicator

def toByte : TickPriceFractionIndicator → UInt8
  | .whole => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .negativeWhole => 0x41
  | .negativeTen => 0x42
  | .negativeHundred => 0x43
  | .negativeThousand => 0x44
  | .negativeTenThousand => 0x45
  | .negativeHundredThousand => 0x46
  | .negativeMillion => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TickPriceFractionIndicator :=
  if byte = 0x30 then .whole
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else if byte = 0x41 then .negativeWhole
  else if byte = 0x42 then .negativeTen
  else if byte = 0x43 then .negativeHundred
  else if byte = 0x44 then .negativeThousand
  else if byte = 0x45 then .negativeTenThousand
  else if byte = 0x46 then .negativeHundredThousand
  else .negativeMillion

def ofByte (byte : UInt8) : TickPriceFractionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TickPriceFractionIndicator) : ofByte value.toByte = value := by
  cases value with
  | whole => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | negativeWhole => decide
  | negativeTen => decide
  | negativeHundred => decide
  | negativeThousand => decide
  | negativeTenThousand => decide
  | negativeHundredThousand => decide
  | negativeMillion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TickPriceFractionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TickPriceFractionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TickPriceFractionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TickPriceFractionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TickPriceFractionIndicator

/-- Login Message: 40 bytes -/
structure LoginMessage where
  user1 : Alpha 16
  pwd1 : Alpha 16
  loginTimestamp : Alpha 6
  protocol : Alpha 2
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.user1
    ++ (Alpha.encode message.pwd1
    ++ (Alpha.encode message.loginTimestamp
    ++ (Alpha.encode message.protocol)))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (user1, bytes) ← Alpha.decode 16 bytes
  let (pwd1, bytes) ← Alpha.decode 16 bytes
  let (loginTimestamp, bytes) ← Alpha.decode 6 bytes
  let (protocol, bytes) ← Alpha.decode 2 bytes
  pure ({ user1, pwd1, loginTimestamp, protocol }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginMessage

/-- Logout Message: 0 bytes -/
structure LogoutMessage where
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (_ : LogoutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutMessage

/-- Login Acknowledgement Message: 0 bytes -/
structure LoginAcknowledgementMessage where
  deriving DecidableEq, Repr

namespace LoginAcknowledgementMessage

def encode (_ : LoginAcknowledgementMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LoginAcknowledgementMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LoginAcknowledgementMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LoginAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LoginAcknowledgementMessage

/-- Logout Acknowledgement Message: 0 bytes -/
structure LogoutAcknowledgementMessage where
  deriving DecidableEq, Repr

namespace LogoutAcknowledgementMessage

def encode (_ : LogoutAcknowledgementMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutAcknowledgementMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutAcknowledgementMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutAcknowledgementMessage

/-- Retransmission Request Message: 20 bytes -/
structure RetransmissionRequestMessage where
  line : Alpha 2
  start : Alpha 9
  end_ : Alpha 9
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  Alpha.encode message.line
    ++ (Alpha.encode message.start
    ++ (Alpha.encode message.end_))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (line, bytes) ← Alpha.decode 2 bytes
  let (start, bytes) ← Alpha.decode 9 bytes
  let (end_, bytes) ← Alpha.decode 9 bytes
  pure ({ line, start, end_ }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Retransmission Begin Message: 0 bytes -/
structure RetransmissionBeginMessage where
  deriving DecidableEq, Repr

namespace RetransmissionBeginMessage

def encode (_ : RetransmissionBeginMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (RetransmissionBeginMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : RetransmissionBeginMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RetransmissionBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end RetransmissionBeginMessage

/-- Retransmission End Message: 0 bytes -/
structure RetransmissionEndMessage where
  deriving DecidableEq, Repr

namespace RetransmissionEndMessage

def encode (_ : RetransmissionEndMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (RetransmissionEndMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : RetransmissionEndMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RetransmissionEndMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end RetransmissionEndMessage

/-- Error Message Message: 84 bytes -/
structure ErrorMessageMessage where
  errorCode : Alpha 4
  errorMsg : Alpha 80
  deriving DecidableEq, Repr

namespace ErrorMessageMessage

def encode (message : ErrorMessageMessage) : List UInt8 :=
  Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorMsg)

def decode (bytes : List UInt8) : Option (ErrorMessageMessage × List UInt8) := do
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorMsg, bytes) ← Alpha.decode 80 bytes
  pure ({ errorCode, errorMsg }, bytes)

@[simp] theorem encode_length (message : ErrorMessageMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErrorMessageMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorMessageMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorMessageMessage

/-- Long Message Header: 12 bytes -/
structure LongMessageHeader where
  messageTimestamp : Alpha 12
  deriving DecidableEq, Repr

namespace LongMessageHeader

def encode (message : LongMessageHeader) : List UInt8 :=
  Alpha.encode message.messageTimestamp

def decode (bytes : List UInt8) : Option (LongMessageHeader × List UInt8) := do
  let (messageTimestamp, bytes) ← Alpha.decode 12 bytes
  pure ({ messageTimestamp }, bytes)

@[simp] theorem encode_length (message : LongMessageHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongMessageHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongMessageHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongMessageHeader

/-- Option Symbol: 20 bytes -/
structure OptionSymbol where
  root : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePrice : Alpha 7
  strikePriceFractionIndicator : StrikePriceFractionIndicator
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace OptionSymbol

def encode (message : OptionSymbol) : List UInt8 :=
  Alpha.encode message.root
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePrice
    ++ (StrikePriceFractionIndicator.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay))))))

def decode (bytes : List UInt8) : Option (OptionSymbol × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← StrikePriceFractionIndicator.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ root, expiryMonth, filler1, strikePrice, strikePriceFractionIndicator, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : OptionSymbol) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, StrikePriceFractionIndicator.encode_length]

theorem encode_length_pos (message : OptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSymbol

/-- Option Trade Message: 83 bytes -/
structure OptionTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler1 : Alpha 1
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, tradeTimestamp, filler1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length, TradePriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeMessage

/-- Future Option Symbol: 20 bytes -/
structure FutureOptionSymbol where
  root : Alpha 6
  symbolMonth : Alpha 1
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : Alpha 1
  strikePrice : Alpha 7
  strikePriceFractionIndicator : StrikePriceFractionIndicator
  deriving DecidableEq, Repr

namespace FutureOptionSymbol

def encode (message : FutureOptionSymbol) : List UInt8 :=
  Alpha.encode message.root
    ++ (Alpha.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.callPutCode
    ++ (Alpha.encode message.strikePrice
    ++ (StrikePriceFractionIndicator.encode message.strikePriceFractionIndicator))))))

def decode (bytes : List UInt8) : Option (FutureOptionSymbol × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← Alpha.decode 1 bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← Alpha.decode 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← StrikePriceFractionIndicator.decode bytes
  pure ({ root, symbolMonth, symbolYear, expiryDay, callPutCode, strikePrice, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : FutureOptionSymbol) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, StrikePriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FutureOptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StrikePriceFractionIndicator.decode_encode, some_bind]
  rfl

end FutureOptionSymbol

/-- Future Options Trade Message: 84 bytes -/
structure FutureOptionsTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  priceIndicatorMarker : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeMessage

def encode (message : FutureOptionsTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber)))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, volume, tradePrice, tradePriceFractionIndicator, priceIndicatorMarker, netChangeSign, netChange, netChangeFractionIndicator, filler6, tradeTimestamp, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length, TradePriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeMessage

/-- Future Product: 11 bytes -/
structure FutureProduct where
  root : Alpha 6
  symbolMonth : Alpha 1
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace FutureProduct

def encode (message : FutureProduct) : List UInt8 :=
  Alpha.encode message.root
    ++ (Alpha.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (FutureProduct × List UInt8) := do
  let (root, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← Alpha.decode 1 bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ root, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : FutureProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FutureProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureProduct

/-- Futures Trade Message: 73 bytes -/
structure FuturesTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeMessage

def encode (message : FuturesTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, TradePriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length]

theorem encode_length_pos (message : FuturesTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeMessage

/-- Strategy Trade Message: 93 bytes -/
structure StrategyTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeMessage

def encode (message : StrategyTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, symbol, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, TradePriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length]

theorem encode_length_pos (message : StrategyTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Option Request For Quote Rfq Message: 42 bytes -/
structure OptionRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : Alpha 1
  deriving DecidableEq, Repr

namespace OptionRequestForQuoteRfqMessage

def encode (message : OptionRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (Alpha.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (OptionRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : OptionRequestForQuoteRfqMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length]

theorem encode_length_pos (message : OptionRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionRequestForQuoteRfqMessage

/-- Future Options Request For Quote Rfq Message: 42 bytes -/
structure FutureOptionsRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionsRequestForQuoteRfqMessage

def encode (message : FutureOptionsRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (Alpha.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (FutureOptionsRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureOptionsRequestForQuoteRfqMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length]

theorem encode_length_pos (message : FutureOptionsRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsRequestForQuoteRfqMessage

/-- Futures Request For Quote Rfq Message: 33 bytes -/
structure FuturesRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  requestedSize : Alpha 8
  requestedMarketSide : Alpha 1
  deriving DecidableEq, Repr

namespace FuturesRequestForQuoteRfqMessage

def encode (message : FuturesRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.requestedSize
    ++ (Alpha.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (FuturesRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FuturesRequestForQuoteRfqMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length]

theorem encode_length_pos (message : FuturesRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesRequestForQuoteRfqMessage

/-- Strategy Request For Quote Rfq Message: 52 bytes -/
structure StrategyRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  symbol : Alpha 30
  requestedSize : Alpha 8
  requestedMarketSide : Alpha 1
  deriving DecidableEq, Repr

namespace StrategyRequestForQuoteRfqMessage

def encode (message : StrategyRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.requestedSize
    ++ (Alpha.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (StrategyRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, symbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : StrategyRequestForQuoteRfqMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyRequestForQuoteRfqMessage

/-- Instrument Schedule Notice Option Message: 40 bytes -/
structure InstrumentScheduleNoticeOptionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeOptionMessage

def encode (message : InstrumentScheduleNoticeOptionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeOptionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeOptionMessage

/-- Instrument Schedule Notice Futures Option Message: 40 bytes -/
structure InstrumentScheduleNoticeFuturesOptionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFuturesOptionMessage

def encode (message : InstrumentScheduleNoticeFuturesOptionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFuturesOptionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFuturesOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFuturesOptionMessage

/-- Instrument Schedule Notice Future Message: 31 bytes -/
structure InstrumentScheduleNoticeFutureMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFutureMessage

def encode (message : InstrumentScheduleNoticeFutureMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFutureMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFutureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFutureMessage

/-- Instrument Schedule Notice Strategy Message: 50 bytes -/
structure InstrumentScheduleNoticeStrategyMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  strategySymbol : Alpha 30
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeStrategyMessage

def encode (message : InstrumentScheduleNoticeStrategyMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeStrategyMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, strategySymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeStrategyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeStrategyMessage

/-- Option Quote Message: 61 bytes -/
structure OptionQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  filler1 : Alpha 1
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.bidPriceQuote
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.instrumentStatusMarker))))))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, filler1, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Future Options Quote Message: 61 bytes -/
structure FutureOptionsQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionsQuoteMessage

def encode (message : FutureOptionsQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.bidPriceQuote
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (Alpha.encode message.filler1))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker, filler1 }, bytes)

@[simp] theorem encode_length (message : FutureOptionsQuoteMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FutureOptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsQuoteMessage

/-- Futures Quote Message: 51 bytes -/
structure FuturesQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace FuturesQuoteMessage

def encode (message : FuturesQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.bidPriceQuote
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker)))))))))

def decode (bytes : List UInt8) : Option (FuturesQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FuturesQuoteMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesQuoteMessage

/-- Strategy Quote Message: 72 bytes -/
structure StrategyQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  symbol : Alpha 30
  bidPriceSign : Alpha 1
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceSign : Alpha 1
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace StrategyQuoteMessage

def encode (message : StrategyQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceQuote
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceQuote
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker)))))))))))

def decode (bytes : List UInt8) : Option (StrategyQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, symbol, bidPriceSign, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceSign, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : StrategyQuoteMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : StrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyQuoteMessage

/-- Market Depth Level: 31 bytes -/
structure MarketDepthLevel where
  levelOfMarketDepth : Alpha 1
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace MarketDepthLevel

def encode (message : MarketDepthLevel) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceQuote
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceQuote
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (MarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : MarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : MarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDepthLevel

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  instrumentStatusMarker : Alpha 1
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevel bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, optionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 314 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Future Options Market Depth Message -/
structure FutureOptionsMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  instrumentStatusMarker : Alpha 1
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthMessage

def encode (message : FutureOptionsMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevel bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, futureOptionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureOptionsMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureOptionsMarketDepthMessage) : (encode message).length ≤ 314 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end FutureOptionsMarketDepthMessage

/-- Futures Market Depth Message -/
structure FuturesMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  instrumentStatusMarker : Alpha 1
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace FuturesMarketDepthMessage

def encode (message : FuturesMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevel bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, futureProduct, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FuturesMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FuturesMarketDepthMessage) : (encode message).length ≤ 305 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FuturesMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end FuturesMarketDepthMessage

/-- Strategy Market Depth Level: 33 bytes -/
structure StrategyMarketDepthLevel where
  levelOfMarketDepth : Alpha 1
  bidPriceSign : Alpha 1
  bidPriceQuote : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : Alpha 1
  askPriceQuote : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace StrategyMarketDepthLevel

def encode (message : StrategyMarketDepthLevel) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceQuote
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceQuote
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceSign, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : StrategyMarketDepthLevel) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : StrategyMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyMarketDepthLevel

/-- Strategy Market Depth Message -/
structure StrategyMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  symbol : Alpha 30
  instrumentStatusMarker : Alpha 1
  strategyMarketDepthLevel : Digited 1 StrategyMarketDepthLevel
  deriving DecidableEq, Repr

namespace StrategyMarketDepthMessage

def encode (message : StrategyMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.strategyMarketDepthLevel.val.length
    ++ (encodeMany StrategyMarketDepthLevel.encode message.strategyMarketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (strategyMarketDepthLevel_, bytes) ← decodeMany StrategyMarketDepthLevel.decode numberOfLevel bytes
  if fits_strategyMarketDepthLevel : strategyMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, symbol, instrumentStatusMarker, strategyMarketDepthLevel := ⟨strategyMarketDepthLevel_, fits_strategyMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyMarketDepthMessage) : (encode message).length ≤ 342 := by
  have bound_strategyMarketDepthLevel := message.strategyMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const StrategyMarketDepthLevel.encode 33 StrategyMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyMarketDepthLevel.encode StrategyMarketDepthLevel.decode StrategyMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyMarketDepthLevel.length_lt]
  rfl

end StrategyMarketDepthMessage

/-- Option Trade Cancellation Message: 74 bytes -/
structure OptionTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler1 : Alpha 1
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, volume, tradePrice, tradePriceFractionIndicator, filler6, tradeTimestamp, filler1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length, TradePriceFractionIndicator.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Future Options Trade Cancellation Message: 75 bytes -/
structure FutureOptionsTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  price : Alpha 7
  priceFractionIndicator : PriceFractionIndicator
  priceIndicatorMarker : Alpha 1
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCancellationMessage

def encode (message : FutureOptionsTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.price
    ++ (PriceFractionIndicator.encode message.priceFractionIndicator
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 7 bytes
  let (priceFractionIndicator, bytes) ← PriceFractionIndicator.decode bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, volume, price, priceFractionIndicator, priceIndicatorMarker, filler6, tradeTimestamp, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCancellationMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length, PriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCancellationMessage

/-- Futures Trade Cancellation Message: 64 bytes -/
structure FuturesTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCancellationMessage

def encode (message : FuturesTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, volume, tradePrice, tradePriceFractionIndicator, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCancellationMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, TradePriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FuturesTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCancellationMessage

/-- Strategy Trade Cancellation Message: 84 bytes -/
structure StrategyTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler1 : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeCancellationMessage

def encode (message : StrategyTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, symbol, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, filler6, tradeTimestamp, filler1, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCancellationMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, TradePriceFractionIndicator.encode_length]

theorem encode_length_pos (message : StrategyTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCancellationMessage

/-- Option Instrument Keys Message: 145 bytes -/
structure OptionInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : MaximumThresholdPriceFractionIndicator
  minimumThresholdPrice : Alpha 7
  minimumThresholdPriceFractionIndicator : MinimumThresholdPriceFractionIndicator
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : TickIncrementFractionIndicator
  optionType : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : Alpha 2
  underlyingSymbolRoot : Alpha 12
  contractSize : Alpha 8
  tickValue : Alpha 7
  tickValueFractionIndicator : TickValueFractionIndicator
  currency : Alpha 3
  deliveryType : Alpha 1
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (MaximumThresholdPriceFractionIndicator.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPrice
    ++ (MinimumThresholdPriceFractionIndicator.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (TickIncrementFractionIndicator.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.optionType
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRoot
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (TickValueFractionIndicator.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.deliveryType)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← MaximumThresholdPriceFractionIndicator.decode bytes
  let (minimumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← MinimumThresholdPriceFractionIndicator.decode bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← TickIncrementFractionIndicator.decode bytes
  let (optionType, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRoot, bytes) ← Alpha.decode 12 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← TickValueFractionIndicator.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPrice, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRoot, contractSize, tickValue, tickValueFractionIndicator, currency, deliveryType }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 145 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length, MaximumThresholdPriceFractionIndicator.encode_length, MinimumThresholdPriceFractionIndicator.encode_length, TickIncrementFractionIndicator.encode_length, TickValueFractionIndicator.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrementFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Future Options Instrument Keys Message: 145 bytes -/
structure FutureOptionsInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  expiryDate : Alpha 6
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : MaximumThresholdPriceFractionIndicator
  minimumThresholdPrice : Alpha 7
  minimumThresholdPriceFractionIndicator : MinimumThresholdPriceFractionIndicator
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : TickIncrementFractionIndicator
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 7
  tickValueFractionIndicator : TickValueFractionIndicator
  currency : Alpha 3
  deliveryType : Alpha 1
  underlyingRootSymbol : Alpha 6
  underlyingSymbolMonth : Alpha 1
  underlyingSymbolYear : Alpha 2
  deriving DecidableEq, Repr

namespace FutureOptionsInstrumentKeysMessage

def encode (message : FutureOptionsInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (MaximumThresholdPriceFractionIndicator.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPrice
    ++ (MinimumThresholdPriceFractionIndicator.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (TickIncrementFractionIndicator.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (TickValueFractionIndicator.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.deliveryType
    ++ (Alpha.encode message.underlyingRootSymbol
    ++ (Alpha.encode message.underlyingSymbolMonth
    ++ (Alpha.encode message.underlyingSymbolYear))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← MaximumThresholdPriceFractionIndicator.decode bytes
  let (minimumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← MinimumThresholdPriceFractionIndicator.decode bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← TickIncrementFractionIndicator.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← TickValueFractionIndicator.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← Alpha.decode 1 bytes
  let (underlyingRootSymbol, bytes) ← Alpha.decode 6 bytes
  let (underlyingSymbolMonth, bytes) ← Alpha.decode 1 bytes
  let (underlyingSymbolYear, bytes) ← Alpha.decode 2 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, expiryDate, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPrice, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValue, tickValueFractionIndicator, currency, deliveryType, underlyingRootSymbol, underlyingSymbolMonth, underlyingSymbolYear }, bytes)

@[simp] theorem encode_length (message : FutureOptionsInstrumentKeysMessage) : (encode message).length = 145 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length, MaximumThresholdPriceFractionIndicator.encode_length, MinimumThresholdPriceFractionIndicator.encode_length, TickIncrementFractionIndicator.encode_length, TickValueFractionIndicator.encode_length]

theorem encode_length_pos (message : FutureOptionsInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrementFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsInstrumentKeysMessage

/-- Underlying Instrument Keys Message: 49 bytes -/
structure UnderlyingInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  deriving DecidableEq, Repr

namespace UnderlyingInstrumentKeysMessage

def encode (message : UnderlyingInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode))))

def decode (bytes : List UInt8) : Option (UnderlyingInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  pure ({ longMessageHeader, exchangeId, groupInstrument, instrument, instrumentExternalCode }, bytes)

@[simp] theorem encode_length (message : UnderlyingInstrumentKeysMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingInstrumentKeysMessage

/-- Associated Product: 11 bytes -/
structure AssociatedProduct where
  rootSymbol : Alpha 6
  symbolMonth : Alpha 1
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace AssociatedProduct

def encode (message : AssociatedProduct) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (AssociatedProduct × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← Alpha.decode 1 bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : AssociatedProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : AssociatedProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AssociatedProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AssociatedProduct

/-- Futures Instrument Keys Message: 147 bytes -/
structure FuturesInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  expiryDate : Alpha 6
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : MaximumThresholdPriceFractionIndicator
  minimumThresholdPrice : Alpha 7
  minimumThresholdPriceFractionIndicator : MinimumThresholdPriceFractionIndicator
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : TickIncrementFractionIndicator
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 7
  tickValueFractionIndicator : TickValueFractionIndicator
  currency : Alpha 3
  underlyingSymbol : Alpha 12
  deliveryType : Alpha 1
  associatedProduct : AssociatedProduct
  deriving DecidableEq, Repr

namespace FuturesInstrumentKeysMessage

def encode (message : FuturesInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (MaximumThresholdPriceFractionIndicator.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPrice
    ++ (MinimumThresholdPriceFractionIndicator.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (TickIncrementFractionIndicator.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (TickValueFractionIndicator.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.deliveryType
    ++ (AssociatedProduct.encode message.associatedProduct))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← MaximumThresholdPriceFractionIndicator.decode bytes
  let (minimumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← MinimumThresholdPriceFractionIndicator.decode bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← TickIncrementFractionIndicator.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← TickValueFractionIndicator.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 12 bytes
  let (deliveryType, bytes) ← Alpha.decode 1 bytes
  let (associatedProduct, bytes) ← AssociatedProduct.decode bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, expiryDate, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPrice, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValue, tickValueFractionIndicator, currency, underlyingSymbol, deliveryType, associatedProduct }, bytes)

@[simp] theorem encode_length (message : FuturesInstrumentKeysMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, MaximumThresholdPriceFractionIndicator.encode_length, MinimumThresholdPriceFractionIndicator.encode_length, TickIncrementFractionIndicator.encode_length, TickValueFractionIndicator.encode_length, AssociatedProduct.encode_length]

theorem encode_length_pos (message : FuturesInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrementFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickValueFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [AssociatedProduct.decode_encode, some_bind]
  rfl

end FuturesInstrumentKeysMessage

/-- Strategy Instrument Leg: 35 bytes -/
structure StrategyInstrumentLeg where
  legRatioSign : Alpha 1
  legRatio : Alpha 4
  legSymbol : Alpha 30
  deriving DecidableEq, Repr

namespace StrategyInstrumentLeg

def encode (message : StrategyInstrumentLeg) : List UInt8 :=
  Alpha.encode message.legRatioSign
    ++ (Alpha.encode message.legRatio
    ++ (Alpha.encode message.legSymbol))

def decode (bytes : List UInt8) : Option (StrategyInstrumentLeg × List UInt8) := do
  let (legRatioSign, bytes) ← Alpha.decode 1 bytes
  let (legRatio, bytes) ← Alpha.decode 4 bytes
  let (legSymbol, bytes) ← Alpha.decode 30 bytes
  pure ({ legRatioSign, legRatio, legSymbol }, bytes)

@[simp] theorem encode_length (message : StrategyInstrumentLeg) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyInstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyInstrumentLeg

/-- Strategy Instrument Keys Message -/
structure StrategyInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  strategySymbol : Alpha 30
  expiryYear : Alpha 2
  expiryMonth : Alpha 1
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : MaximumThresholdPriceFractionIndicator
  minimumThresholdPrice : Alpha 7
  minimumThresholdPriceFractionIndicator : MinimumThresholdPriceFractionIndicator
  tickIncrement : Alpha 7
  tickIncrementFractionIndicator : TickIncrementFractionIndicator
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  strategyAllowImplied : Alpha 1
  strategyCode : Alpha 2
  strategyInstrumentLeg : Digited 2 StrategyInstrumentLeg
  deriving DecidableEq, Repr

namespace StrategyInstrumentKeysMessage

def encode (message : StrategyInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPrice
    ++ (MaximumThresholdPriceFractionIndicator.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPrice
    ++ (MinimumThresholdPriceFractionIndicator.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (TickIncrementFractionIndicator.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.strategyAllowImplied
    ++ (Alpha.encode message.strategyCode
    ++ (encodeDigits 2 message.strategyInstrumentLeg.val.length
    ++ (encodeMany StrategyInstrumentLeg.encode message.strategyInstrumentLeg.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← MaximumThresholdPriceFractionIndicator.decode bytes
  let (minimumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← MinimumThresholdPriceFractionIndicator.decode bytes
  let (tickIncrement, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← TickIncrementFractionIndicator.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (strategyAllowImplied, bytes) ← Alpha.decode 1 bytes
  let (strategyCode, bytes) ← Alpha.decode 2 bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (strategyInstrumentLeg_, bytes) ← decodeMany StrategyInstrumentLeg.decode numberOfLegs bytes
  if fits_strategyInstrumentLeg : strategyInstrumentLeg_.length < 10 ^ 2 then
    pure ({ longMessageHeader, exchangeId, strategySymbol, expiryYear, expiryMonth, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPrice, maximumThresholdPriceFractionIndicator, minimumThresholdPrice, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, strategyAllowImplied, strategyCode, strategyInstrumentLeg := ⟨strategyInstrumentLeg_, fits_strategyInstrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyInstrumentKeysMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyInstrumentKeysMessage) : (encode message).length ≤ 3592 := by
  have bound_strategyInstrumentLeg := message.strategyInstrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionIndicator.encode_length, MinimumThresholdPriceFractionIndicator.encode_length, TickIncrementFractionIndicator.encode_length, encodeDigits_length, encodeMany_length_const StrategyInstrumentLeg.encode 35 StrategyInstrumentLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrementFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyInstrumentLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyInstrumentLeg.encode StrategyInstrumentLeg.decode StrategyInstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyInstrumentLeg.length_lt]
  rfl

end StrategyInstrumentKeysMessage

/-- Option Summary Message: 141 bytes -/
structure OptionSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  optionSymbol : OptionSymbol
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  lastPrice : Alpha 7
  lastPriceFractionIndicator : LastPriceFractionIndicator
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Alpha 1
  volume : Alpha 8
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  openPrice : Alpha 7
  openPriceFractionIndicator : OpenPriceFractionIndicator
  highPrice : Alpha 7
  highPriceFractionIndicator : HighPriceFractionIndicator
  lowPrice : Alpha 7
  lowPriceFractionIndicator : LowPriceFractionIndicator
  optionMarker : Alpha 2
  settlementPrice : Alpha 7
  settlementPriceFractionIndicator : SettlementPriceFractionIndicator
  previousSettlementPrice : Alpha 7
  previousSettlementPriceFractionIndicator : PreviousSettlementPriceFractionIndicator
  reason : Alpha 1
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.bidPriceSummary
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (LastPriceFractionIndicator.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Alpha.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (OpenPriceFractionIndicator.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (HighPriceFractionIndicator.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (LowPriceFractionIndicator.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.settlementPrice
    ++ (SettlementPriceFractionIndicator.encode message.settlementPriceFractionIndicator
    ++ (Alpha.encode message.previousSettlementPrice
    ++ (PreviousSettlementPriceFractionIndicator.encode message.previousSettlementPriceFractionIndicator
    ++ (Alpha.encode message.reason)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← LastPriceFractionIndicator.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (openPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← OpenPriceFractionIndicator.decode bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← HighPriceFractionIndicator.decode bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← LowPriceFractionIndicator.decode bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (settlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← SettlementPriceFractionIndicator.decode bytes
  let (previousSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← PreviousSettlementPriceFractionIndicator.decode bytes
  let (reason, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, openInterestDate, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, optionMarker, settlementPrice, settlementPriceFractionIndicator, previousSettlementPrice, previousSettlementPriceFractionIndicator, reason }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 141 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, OptionSymbol.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length, LastPriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length, OpenPriceFractionIndicator.encode_length, HighPriceFractionIndicator.encode_length, LowPriceFractionIndicator.encode_length, SettlementPriceFractionIndicator.encode_length, PreviousSettlementPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Future Options Summary Message: 141 bytes -/
structure FutureOptionsSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureOptionSymbol : FutureOptionSymbol
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  lastPrice : Alpha 7
  lastPriceFractionIndicator : LastPriceFractionIndicator
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Alpha 1
  volume : Alpha 8
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  openingPrice : Alpha 7
  openingPriceFractionIndicator : OpeningPriceFractionIndicator
  highPrice : Alpha 7
  highPriceFractionIndicator : HighPriceFractionIndicator
  lowPrice : Alpha 7
  lowPriceFractionIndicator : LowPriceFractionIndicator
  filler2 : Alpha 2
  settlementPrice : Alpha 7
  settlementPriceFractionIndicator : SettlementPriceFractionIndicator
  previousSettlementPrice : Alpha 7
  previousSettlementPriceFractionIndicator : PreviousSettlementPriceFractionIndicator
  reason : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionsSummaryMessage

def encode (message : FutureOptionsSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.bidPriceSummary
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (LastPriceFractionIndicator.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Alpha.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openingPrice
    ++ (OpeningPriceFractionIndicator.encode message.openingPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (HighPriceFractionIndicator.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (LowPriceFractionIndicator.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.settlementPrice
    ++ (SettlementPriceFractionIndicator.encode message.settlementPriceFractionIndicator
    ++ (Alpha.encode message.previousSettlementPrice
    ++ (PreviousSettlementPriceFractionIndicator.encode message.previousSettlementPriceFractionIndicator
    ++ (Alpha.encode message.reason)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← LastPriceFractionIndicator.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (openingPrice, bytes) ← Alpha.decode 7 bytes
  let (openingPriceFractionIndicator, bytes) ← OpeningPriceFractionIndicator.decode bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← HighPriceFractionIndicator.decode bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← LowPriceFractionIndicator.decode bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (settlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← SettlementPriceFractionIndicator.decode bytes
  let (previousSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← PreviousSettlementPriceFractionIndicator.decode bytes
  let (reason, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, openInterestDate, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openingPrice, openingPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, filler2, settlementPrice, settlementPriceFractionIndicator, previousSettlementPrice, previousSettlementPriceFractionIndicator, reason }, bytes)

@[simp] theorem encode_length (message : FutureOptionsSummaryMessage) : (encode message).length = 141 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureOptionSymbol.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length, LastPriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length, OpeningPriceFractionIndicator.encode_length, HighPriceFractionIndicator.encode_length, LowPriceFractionIndicator.encode_length, SettlementPriceFractionIndicator.encode_length, PreviousSettlementPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsSummaryMessage

/-- Futures Summary Message: 137 bytes -/
structure FuturesSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  lastPrice : Alpha 7
  lastPriceFractionIndicator : LastPriceFractionIndicator
  openPrice : Alpha 7
  openPriceFractionIndicator : OpenPriceFractionIndicator
  highPrice : Alpha 7
  highPriceFractionIndicator : HighPriceFractionIndicator
  lowPrice : Alpha 7
  lowPriceFractionIndicator : LowPriceFractionIndicator
  settlementPrice : Alpha 7
  settlementPriceFractionIndicator : SettlementPriceFractionIndicator
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  volume : Alpha 8
  previousSettlement : Alpha 7
  previousSettlementFractionIndicator : PreviousSettlementFractionIndicator
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  reason : Alpha 1
  externalPriceAtSource : Alpha 7
  externalPriceFractionIndicator : ExternalPriceFractionIndicator
  deriving DecidableEq, Repr

namespace FuturesSummaryMessage

def encode (message : FuturesSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.bidPriceSummary
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (LastPriceFractionIndicator.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (OpenPriceFractionIndicator.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (HighPriceFractionIndicator.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (LowPriceFractionIndicator.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.settlementPrice
    ++ (SettlementPriceFractionIndicator.encode message.settlementPriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.previousSettlement
    ++ (PreviousSettlementFractionIndicator.encode message.previousSettlementFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Alpha.encode message.reason
    ++ (Alpha.encode message.externalPriceAtSource
    ++ (ExternalPriceFractionIndicator.encode message.externalPriceFractionIndicator)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FuturesSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← LastPriceFractionIndicator.decode bytes
  let (openPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← OpenPriceFractionIndicator.decode bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← HighPriceFractionIndicator.decode bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← LowPriceFractionIndicator.decode bytes
  let (settlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← SettlementPriceFractionIndicator.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlement, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementFractionIndicator, bytes) ← PreviousSettlementFractionIndicator.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (reason, bytes) ← Alpha.decode 1 bytes
  let (externalPriceAtSource, bytes) ← Alpha.decode 7 bytes
  let (externalPriceFractionIndicator, bytes) ← ExternalPriceFractionIndicator.decode bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, settlementPrice, settlementPriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume, previousSettlement, previousSettlementFractionIndicator, openInterest, openInterestDate, reason, externalPriceAtSource, externalPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : FuturesSummaryMessage) : (encode message).length = 137 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length, LastPriceFractionIndicator.encode_length, OpenPriceFractionIndicator.encode_length, HighPriceFractionIndicator.encode_length, LowPriceFractionIndicator.encode_length, SettlementPriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length, PreviousSettlementFractionIndicator.encode_length, ExternalPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : FuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ExternalPriceFractionIndicator.decode_encode, some_bind]
  rfl

end FuturesSummaryMessage

/-- Strategy Summary Message: 125 bytes -/
structure StrategySummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  strategySymbol : Alpha 30
  bidPriceSign : Alpha 1
  bidPriceSummary : Alpha 7
  bidPriceFractionIndicator : BidPriceFractionIndicator
  bidSize : Alpha 5
  askPriceSign : Alpha 1
  askPriceSummary : Alpha 7
  askPriceFractionIndicator : AskPriceFractionIndicator
  askSize : Alpha 5
  lastPriceSign : Alpha 1
  lastPrice : Alpha 7
  lastPriceFractionIndicator : LastPriceFractionIndicator
  openPriceSign : Alpha 1
  openPrice : Alpha 7
  openPriceFractionIndicator : OpenPriceFractionIndicator
  highPriceSign : Alpha 1
  highPrice : Alpha 7
  highPriceFractionIndicator : HighPriceFractionIndicator
  lowPriceSign : Alpha 1
  lowPrice : Alpha 7
  lowPriceFractionIndicator : LowPriceFractionIndicator
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  volume : Alpha 8
  reason : Alpha 1
  deriving DecidableEq, Repr

namespace StrategySummaryMessage

def encode (message : StrategySummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceSummary
    ++ (BidPriceFractionIndicator.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceSummary
    ++ (AskPriceFractionIndicator.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPriceSign
    ++ (Alpha.encode message.lastPrice
    ++ (LastPriceFractionIndicator.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPriceSign
    ++ (Alpha.encode message.openPrice
    ++ (OpenPriceFractionIndicator.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPriceSign
    ++ (Alpha.encode message.highPrice
    ++ (HighPriceFractionIndicator.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPriceSign
    ++ (Alpha.encode message.lowPrice
    ++ (LowPriceFractionIndicator.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.reason)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (StrategySummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← BidPriceFractionIndicator.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← AskPriceFractionIndicator.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← LastPriceFractionIndicator.decode bytes
  let (openPriceSign, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← OpenPriceFractionIndicator.decode bytes
  let (highPriceSign, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← HighPriceFractionIndicator.decode bytes
  let (lowPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← LowPriceFractionIndicator.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (reason, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, strategySymbol, bidPriceSign, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSign, askPriceSummary, askPriceFractionIndicator, askSize, lastPriceSign, lastPrice, lastPriceFractionIndicator, openPriceSign, openPrice, openPriceFractionIndicator, highPriceSign, highPrice, highPriceFractionIndicator, lowPriceSign, lowPrice, lowPriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume, reason }, bytes)

@[simp] theorem encode_length (message : StrategySummaryMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, BidPriceFractionIndicator.encode_length, AskPriceFractionIndicator.encode_length, LastPriceFractionIndicator.encode_length, OpenPriceFractionIndicator.encode_length, HighPriceFractionIndicator.encode_length, LowPriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length]

theorem encode_length_pos (message : StrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : StrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategySummaryMessage

/-- Beginning Of Options Summary Message: 13 bytes -/
structure BeginningOfOptionsSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfOptionsSummaryMessage

def encode (message : BeginningOfOptionsSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfOptionsSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfOptionsSummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfOptionsSummaryMessage

/-- Beginning Of Future Options Summary Message: 13 bytes -/
structure BeginningOfFutureOptionsSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfFutureOptionsSummaryMessage

def encode (message : BeginningOfFutureOptionsSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfFutureOptionsSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfFutureOptionsSummaryMessage

/-- Beginning Of Futures Summary Message: 13 bytes -/
structure BeginningOfFuturesSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfFuturesSummaryMessage

def encode (message : BeginningOfFuturesSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfFuturesSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFuturesSummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfFuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfFuturesSummaryMessage

/-- Beginning Of Strategy Summary Message: 13 bytes -/
structure BeginningOfStrategySummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfStrategySummaryMessage

def encode (message : BeginningOfStrategySummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfStrategySummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfStrategySummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfStrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfStrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfStrategySummaryMessage

/-- Futures Trade Correction Message: 73 bytes -/
structure FuturesTradeCorrectionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePrice : Alpha 7
  tradePriceFractionIndicator : TradePriceFractionIndicator
  netChangeSign : Alpha 1
  netChange : Alpha 7
  netChangeFractionIndicator : NetChangeFractionIndicator
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCorrectionMessage

def encode (message : FuturesTradeCorrectionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (TradePriceFractionIndicator.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (NetChangeFractionIndicator.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCorrectionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← TradePriceFractionIndicator.decode bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← NetChangeFractionIndicator.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCorrectionMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length, FutureProduct.encode_length, TradePriceFractionIndicator.encode_length, NetChangeFractionIndicator.encode_length]

theorem encode_length_pos (message : FuturesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCorrectionMessage

/-- Group Status Message: 20 bytes -/
structure GroupStatusMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  groupStatus : Alpha 1
  deriving DecidableEq, Repr

namespace GroupStatusMessage

def encode (message : GroupStatusMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.groupStatus)))

def decode (bytes : List UInt8) : Option (GroupStatusMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, rootSymbol, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupStatusMessage

/-- Group Status Strategies Message: 16 bytes -/
structure GroupStatusStrategiesMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  groupInstrument : Alpha 2
  groupStatus : Alpha 1
  deriving DecidableEq, Repr

namespace GroupStatusStrategiesMessage

def encode (message : GroupStatusStrategiesMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.groupStatus)))

def decode (bytes : List UInt8) : Option (GroupStatusStrategiesMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (groupStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, groupInstrument, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusStrategiesMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GroupStatusStrategiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusStrategiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupStatusStrategiesMessage

/-- Regular Text Bulletin: 80 bytes -/
structure RegularTextBulletin where
  regularBulletinContents : Alpha 79
  continueMarker : Alpha 1
  deriving DecidableEq, Repr

namespace RegularTextBulletin

def encode (message : RegularTextBulletin) : List UInt8 :=
  Alpha.encode message.regularBulletinContents
    ++ (Alpha.encode message.continueMarker)

def decode (bytes : List UInt8) : Option (RegularTextBulletin × List UInt8) := do
  let (regularBulletinContents, bytes) ← Alpha.decode 79 bytes
  let (continueMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ regularBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : RegularTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RegularTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegularTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RegularTextBulletin

/-- Special Text Bulletin: 80 bytes -/
structure SpecialTextBulletin where
  symbol : Alpha 30
  specialBulletinContents : Alpha 49
  continueMarker : Alpha 1
  deriving DecidableEq, Repr

namespace SpecialTextBulletin

def encode (message : SpecialTextBulletin) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.specialBulletinContents
    ++ (Alpha.encode message.continueMarker))

def decode (bytes : List UInt8) : Option (SpecialTextBulletin × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (specialBulletinContents, bytes) ← Alpha.decode 49 bytes
  let (continueMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ symbol, specialBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : SpecialTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SpecialTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpecialTextBulletin

/-- Any Bulletin, selected by Bulletin Type -/
inductive Bulletin where
  | regularTextBulletin (message : RegularTextBulletin) -- "1" 0x31
  | specialTextBulletin (message : SpecialTextBulletin) -- "2" 0x32
  deriving DecidableEq, Repr

namespace Bulletin

/-- The Bulletin Type each message is sent under -/
def tag : Bulletin → BitVec 8
  | .regularTextBulletin _ => 49
  | .specialTextBulletin _ => 50

def encode : Bulletin → List UInt8
  | .regularTextBulletin message => RegularTextBulletin.encode message
  | .specialTextBulletin message => SpecialTextBulletin.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Bulletin) : (encode message).length ≤ 80 := by
  cases message with
  | regularTextBulletin inner =>
    simp only [encode, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [encode, SpecialTextBulletin.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Bulletin × List UInt8) :=
  if tag = 49 then (RegularTextBulletin.decode bytes).map fun (message, rest) => (.regularTextBulletin message, rest)
  else if tag = 50 then (SpecialTextBulletin.decode bytes).map fun (message, rest) => (.specialTextBulletin message, rest)
  else none

@[simp] theorem decode_encode (message : Bulletin) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Bulletin

/-- Bulletins Message -/
structure BulletinsMessage where
  longMessageHeader : LongMessageHeader
  reserved : Alpha 1
  bulletin : Bulletin
  deriving DecidableEq, Repr

namespace BulletinsMessage

def encode (message : BulletinsMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.reserved
    ++ (encodeUInt 1 (Bulletin.tag message.bulletin)
    ++ (Bulletin.encode message.bulletin)))

def decode (bytes : List UInt8) : Option (BulletinsMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (bulletinType, bytes) ← decodeUInt 1 bytes
  let (bulletin, bytes) ← Bulletin.decode bulletinType bytes
  pure ({ longMessageHeader, reserved, bulletin }, bytes)

theorem encode_length_pos (message : BulletinsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulletinsMessage) : (encode message).length ≤ 94 := by
  unfold encode
  cases message.bulletin with
  | regularTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, encodeUInt_length, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, encodeUInt_length, SpecialTextBulletin.encode_length]
    omega

@[simp] theorem decode_encode (message : BulletinsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Bulletin.decode_encode, some_bind]
  rfl

end BulletinsMessage

/-- End Of Sales Message: 19 bytes -/
structure EndOfSalesMessage where
  longMessageHeader : LongMessageHeader
  reserved : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfSalesMessage

def encode (message : EndOfSalesMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.reserved
    ++ (Alpha.encode message.time))

def decode (bytes : List UInt8) : Option (EndOfSalesMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, reserved, time }, bytes)

@[simp] theorem encode_length (message : EndOfSalesMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfSalesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSalesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSalesMessage

/-- Tick Entry: 16 bytes -/
structure TickEntry where
  minPrice : Alpha 7
  minPriceFractionIndicator : MinPriceFractionIndicator
  tickPrice : Alpha 7
  tickPriceFractionIndicator : TickPriceFractionIndicator
  deriving DecidableEq, Repr

namespace TickEntry

def encode (message : TickEntry) : List UInt8 :=
  Alpha.encode message.minPrice
    ++ (MinPriceFractionIndicator.encode message.minPriceFractionIndicator
    ++ (Alpha.encode message.tickPrice
    ++ (TickPriceFractionIndicator.encode message.tickPriceFractionIndicator)))

def decode (bytes : List UInt8) : Option (TickEntry × List UInt8) := do
  let (minPrice, bytes) ← Alpha.decode 7 bytes
  let (minPriceFractionIndicator, bytes) ← MinPriceFractionIndicator.decode bytes
  let (tickPrice, bytes) ← Alpha.decode 7 bytes
  let (tickPriceFractionIndicator, bytes) ← TickPriceFractionIndicator.decode bytes
  pure ({ minPrice, minPriceFractionIndicator, tickPrice, tickPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickEntry) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MinPriceFractionIndicator.encode_length, TickPriceFractionIndicator.encode_length]

theorem encode_length_pos (message : TickEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinPriceFractionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TickPriceFractionIndicator.decode_encode, some_bind]
  rfl

end TickEntry

/-- Tick Table Message -/
structure TickTableMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  tickTableName : Alpha 50
  tickTableShortName : Alpha 2
  tickEntry : Digited 2 TickEntry
  deriving DecidableEq, Repr

namespace TickTableMessage

def encode (message : TickTableMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.tickTableName
    ++ (Alpha.encode message.tickTableShortName
    ++ (encodeDigits 2 message.tickEntry.val.length
    ++ (encodeMany TickEntry.encode message.tickEntry.val)))))

def decode (bytes : List UInt8) : Option (TickTableMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (tickTableName, bytes) ← Alpha.decode 50 bytes
  let (tickTableShortName, bytes) ← Alpha.decode 2 bytes
  let (nbEntries, bytes) ← decodeDigits 2 bytes
  let (tickEntry_, bytes) ← decodeMany TickEntry.decode nbEntries bytes
  if fits_tickEntry : tickEntry_.length < 10 ^ 2 then
    pure ({ longMessageHeader, exchangeId, tickTableName, tickTableShortName, tickEntry := ⟨tickEntry_, fits_tickEntry⟩ }, bytes)
  else none

theorem encode_length_pos (message : TickTableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickTableMessage) : (encode message).length ≤ 1651 := by
  have bound_tickEntry := message.tickEntry.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const TickEntry.encode 16 TickEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : TickTableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.tickEntry.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany TickEntry.encode TickEntry.decode TickEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tickEntry.length_lt]
  rfl

end TickTableMessage

/-- End Of Transmission Message: 19 bytes -/
structure EndOfTransmissionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmissionMessage

def encode (message : EndOfTransmissionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.time))

def decode (bytes : List UInt8) : Option (EndOfTransmissionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmissionMessage

/-- Circuit Assurance Message: 18 bytes -/
structure CircuitAssuranceMessage where
  longMessageHeader : LongMessageHeader
  time : Alpha 6
  deriving DecidableEq, Repr

namespace CircuitAssuranceMessage

def encode (message : CircuitAssuranceMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (CircuitAssuranceMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, time }, bytes)

@[simp] theorem encode_length (message : CircuitAssuranceMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CircuitAssuranceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CircuitAssuranceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CircuitAssuranceMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | loginMessage (message : LoginMessage) -- "LI" 0x4C49
  | logoutMessage (message : LogoutMessage) -- "LO" 0x4C4F
  | loginAcknowledgementMessage (message : LoginAcknowledgementMessage) -- "KI" 0x4B49
  | logoutAcknowledgementMessage (message : LogoutAcknowledgementMessage) -- "KO" 0x4B4F
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- "RT" 0x5254
  | retransmissionBeginMessage (message : RetransmissionBeginMessage) -- "RB" 0x5242
  | retransmissionEndMessage (message : RetransmissionEndMessage) -- "RE" 0x5245
  | errorMessageMessage (message : ErrorMessageMessage) -- "ER" 0x4552
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | futureOptionsTradeMessage (message : FutureOptionsTradeMessage) -- "CB" 0x4342
  | futuresTradeMessage (message : FuturesTradeMessage) -- "CF" 0x4346
  | strategyTradeMessage (message : StrategyTradeMessage) -- "CS" 0x4353
  | optionRequestForQuoteRfqMessage (message : OptionRequestForQuoteRfqMessage) -- "D " 0x4420
  | futureOptionsRequestForQuoteRfqMessage (message : FutureOptionsRequestForQuoteRfqMessage) -- "DB" 0x4442
  | futuresRequestForQuoteRfqMessage (message : FuturesRequestForQuoteRfqMessage) -- "DF" 0x4446
  | strategyRequestForQuoteRfqMessage (message : StrategyRequestForQuoteRfqMessage) -- "DS" 0x4453
  | instrumentScheduleNoticeOptionMessage (message : InstrumentScheduleNoticeOptionMessage) -- "E " 0x4520
  | instrumentScheduleNoticeFuturesOptionMessage (message : InstrumentScheduleNoticeFuturesOptionMessage) -- "EB" 0x4542
  | instrumentScheduleNoticeFutureMessage (message : InstrumentScheduleNoticeFutureMessage) -- "EF" 0x4546
  | instrumentScheduleNoticeStrategyMessage (message : InstrumentScheduleNoticeStrategyMessage) -- "ES" 0x4553
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | futureOptionsQuoteMessage (message : FutureOptionsQuoteMessage) -- "FB" 0x4642
  | futuresQuoteMessage (message : FuturesQuoteMessage) -- "FF" 0x4646
  | strategyQuoteMessage (message : StrategyQuoteMessage) -- "FS" 0x4653
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | futureOptionsMarketDepthMessage (message : FutureOptionsMarketDepthMessage) -- "HB" 0x4842
  | futuresMarketDepthMessage (message : FuturesMarketDepthMessage) -- "HF" 0x4846
  | strategyMarketDepthMessage (message : StrategyMarketDepthMessage) -- "HS" 0x4853
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | futureOptionsTradeCancellationMessage (message : FutureOptionsTradeCancellationMessage) -- "IB" 0x4942
  | futuresTradeCancellationMessage (message : FuturesTradeCancellationMessage) -- "IF" 0x4946
  | strategyTradeCancellationMessage (message : StrategyTradeCancellationMessage) -- "IS" 0x4953
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | futureOptionsInstrumentKeysMessage (message : FutureOptionsInstrumentKeysMessage) -- "JB" 0x4A42
  | underlyingInstrumentKeysMessage (message : UnderlyingInstrumentKeysMessage) -- "JE" 0x4A45
  | futuresInstrumentKeysMessage (message : FuturesInstrumentKeysMessage) -- "JF" 0x4A46
  | strategyInstrumentKeysMessage (message : StrategyInstrumentKeysMessage) -- "JS" 0x4A53
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | futureOptionsSummaryMessage (message : FutureOptionsSummaryMessage) -- "NB" 0x4E42
  | futuresSummaryMessage (message : FuturesSummaryMessage) -- "NF" 0x4E46
  | strategySummaryMessage (message : StrategySummaryMessage) -- "NS" 0x4E53
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfFutureOptionsSummaryMessage (message : BeginningOfFutureOptionsSummaryMessage) -- "QB" 0x5142
  | beginningOfFuturesSummaryMessage (message : BeginningOfFuturesSummaryMessage) -- "QF" 0x5146
  | beginningOfStrategySummaryMessage (message : BeginningOfStrategySummaryMessage) -- "QS" 0x5153
  | futuresTradeCorrectionMessage (message : FuturesTradeCorrectionMessage) -- "XF" 0x5846
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | groupStatusStrategiesMessage (message : GroupStatusStrategiesMessage) -- "GS" 0x4753
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | tickTableMessage (message : TickTableMessage) -- "TT" 0x5454
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .loginMessage _ => 19529
  | .logoutMessage _ => 19535
  | .loginAcknowledgementMessage _ => 19273
  | .logoutAcknowledgementMessage _ => 19279
  | .retransmissionRequestMessage _ => 21076
  | .retransmissionBeginMessage _ => 21058
  | .retransmissionEndMessage _ => 21061
  | .errorMessageMessage _ => 17746
  | .optionTradeMessage _ => 17184
  | .futureOptionsTradeMessage _ => 17218
  | .futuresTradeMessage _ => 17222
  | .strategyTradeMessage _ => 17235
  | .optionRequestForQuoteRfqMessage _ => 17440
  | .futureOptionsRequestForQuoteRfqMessage _ => 17474
  | .futuresRequestForQuoteRfqMessage _ => 17478
  | .strategyRequestForQuoteRfqMessage _ => 17491
  | .instrumentScheduleNoticeOptionMessage _ => 17696
  | .instrumentScheduleNoticeFuturesOptionMessage _ => 17730
  | .instrumentScheduleNoticeFutureMessage _ => 17734
  | .instrumentScheduleNoticeStrategyMessage _ => 17747
  | .optionQuoteMessage _ => 17952
  | .futureOptionsQuoteMessage _ => 17986
  | .futuresQuoteMessage _ => 17990
  | .strategyQuoteMessage _ => 18003
  | .optionMarketDepthMessage _ => 18464
  | .futureOptionsMarketDepthMessage _ => 18498
  | .futuresMarketDepthMessage _ => 18502
  | .strategyMarketDepthMessage _ => 18515
  | .optionTradeCancellationMessage _ => 18720
  | .futureOptionsTradeCancellationMessage _ => 18754
  | .futuresTradeCancellationMessage _ => 18758
  | .strategyTradeCancellationMessage _ => 18771
  | .optionInstrumentKeysMessage _ => 18976
  | .futureOptionsInstrumentKeysMessage _ => 19010
  | .underlyingInstrumentKeysMessage _ => 19013
  | .futuresInstrumentKeysMessage _ => 19014
  | .strategyInstrumentKeysMessage _ => 19027
  | .optionSummaryMessage _ => 20000
  | .futureOptionsSummaryMessage _ => 20034
  | .futuresSummaryMessage _ => 20038
  | .strategySummaryMessage _ => 20051
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfFutureOptionsSummaryMessage _ => 20802
  | .beginningOfFuturesSummaryMessage _ => 20806
  | .beginningOfStrategySummaryMessage _ => 20819
  | .futuresTradeCorrectionMessage _ => 22598
  | .groupStatusMessage _ => 18258
  | .groupStatusStrategiesMessage _ => 18259
  | .bulletinsMessage _ => 19488
  | .endOfSalesMessage _ => 21280
  | .tickTableMessage _ => 21588
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048

def encode : MessageBody → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .loginAcknowledgementMessage message => LoginAcknowledgementMessage.encode message
  | .logoutAcknowledgementMessage message => LogoutAcknowledgementMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .retransmissionBeginMessage message => RetransmissionBeginMessage.encode message
  | .retransmissionEndMessage message => RetransmissionEndMessage.encode message
  | .errorMessageMessage message => ErrorMessageMessage.encode message
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .futureOptionsTradeMessage message => FutureOptionsTradeMessage.encode message
  | .futuresTradeMessage message => FuturesTradeMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .optionRequestForQuoteRfqMessage message => OptionRequestForQuoteRfqMessage.encode message
  | .futureOptionsRequestForQuoteRfqMessage message => FutureOptionsRequestForQuoteRfqMessage.encode message
  | .futuresRequestForQuoteRfqMessage message => FuturesRequestForQuoteRfqMessage.encode message
  | .strategyRequestForQuoteRfqMessage message => StrategyRequestForQuoteRfqMessage.encode message
  | .instrumentScheduleNoticeOptionMessage message => InstrumentScheduleNoticeOptionMessage.encode message
  | .instrumentScheduleNoticeFuturesOptionMessage message => InstrumentScheduleNoticeFuturesOptionMessage.encode message
  | .instrumentScheduleNoticeFutureMessage message => InstrumentScheduleNoticeFutureMessage.encode message
  | .instrumentScheduleNoticeStrategyMessage message => InstrumentScheduleNoticeStrategyMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .futureOptionsQuoteMessage message => FutureOptionsQuoteMessage.encode message
  | .futuresQuoteMessage message => FuturesQuoteMessage.encode message
  | .strategyQuoteMessage message => StrategyQuoteMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .futureOptionsMarketDepthMessage message => FutureOptionsMarketDepthMessage.encode message
  | .futuresMarketDepthMessage message => FuturesMarketDepthMessage.encode message
  | .strategyMarketDepthMessage message => StrategyMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .futureOptionsTradeCancellationMessage message => FutureOptionsTradeCancellationMessage.encode message
  | .futuresTradeCancellationMessage message => FuturesTradeCancellationMessage.encode message
  | .strategyTradeCancellationMessage message => StrategyTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .futureOptionsInstrumentKeysMessage message => FutureOptionsInstrumentKeysMessage.encode message
  | .underlyingInstrumentKeysMessage message => UnderlyingInstrumentKeysMessage.encode message
  | .futuresInstrumentKeysMessage message => FuturesInstrumentKeysMessage.encode message
  | .strategyInstrumentKeysMessage message => StrategyInstrumentKeysMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .futureOptionsSummaryMessage message => FutureOptionsSummaryMessage.encode message
  | .futuresSummaryMessage message => FuturesSummaryMessage.encode message
  | .strategySummaryMessage message => StrategySummaryMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfFutureOptionsSummaryMessage message => BeginningOfFutureOptionsSummaryMessage.encode message
  | .beginningOfFuturesSummaryMessage message => BeginningOfFuturesSummaryMessage.encode message
  | .beginningOfStrategySummaryMessage message => BeginningOfStrategySummaryMessage.encode message
  | .futuresTradeCorrectionMessage message => FuturesTradeCorrectionMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .groupStatusStrategiesMessage message => GroupStatusStrategiesMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .tickTableMessage message => TickTableMessage.encode message
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3592 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | loginAcknowledgementMessage inner =>
    simp only [encode, LoginAcknowledgementMessage.encode_length]
    omega
  | logoutAcknowledgementMessage inner =>
    simp only [encode, LogoutAcknowledgementMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionBeginMessage inner =>
    simp only [encode, RetransmissionBeginMessage.encode_length]
    omega
  | retransmissionEndMessage inner =>
    simp only [encode, RetransmissionEndMessage.encode_length]
    omega
  | errorMessageMessage inner =>
    simp only [encode, ErrorMessageMessage.encode_length]
    omega
  | optionTradeMessage inner =>
    simp only [encode, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [encode, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [encode, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [encode, StrategyTradeMessage.encode_length]
    omega
  | optionRequestForQuoteRfqMessage inner =>
    simp only [encode, OptionRequestForQuoteRfqMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteRfqMessage inner =>
    simp only [encode, FutureOptionsRequestForQuoteRfqMessage.encode_length]
    omega
  | futuresRequestForQuoteRfqMessage inner =>
    simp only [encode, FuturesRequestForQuoteRfqMessage.encode_length]
    omega
  | strategyRequestForQuoteRfqMessage inner =>
    simp only [encode, StrategyRequestForQuoteRfqMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [encode, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [encode, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [encode, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [encode, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [encode, StrategyQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [encode, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [encode, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futuresTradeCancellationMessage inner =>
    simp only [encode, FuturesTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [encode, StrategyTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [encode, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [encode, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [encode, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [encode, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionSummaryMessage inner =>
    simp only [encode, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [encode, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [encode, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    simp only [encode, StrategySummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [encode, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [encode, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [encode, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [encode, GroupStatusStrategiesMessage.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfSalesMessage inner =>
    simp only [encode, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfTransmissionMessage inner =>
    simp only [encode, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [encode, CircuitAssuranceMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 19529 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 19535 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 19273 then (LoginAcknowledgementMessage.decode bytes).map fun (message, rest) => (.loginAcknowledgementMessage message, rest)
  else if tag = 19279 then (LogoutAcknowledgementMessage.decode bytes).map fun (message, rest) => (.logoutAcknowledgementMessage message, rest)
  else if tag = 21076 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 21058 then (RetransmissionBeginMessage.decode bytes).map fun (message, rest) => (.retransmissionBeginMessage message, rest)
  else if tag = 21061 then (RetransmissionEndMessage.decode bytes).map fun (message, rest) => (.retransmissionEndMessage message, rest)
  else if tag = 17746 then (ErrorMessageMessage.decode bytes).map fun (message, rest) => (.errorMessageMessage message, rest)
  else if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17218 then (FutureOptionsTradeMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeMessage message, rest)
  else if tag = 17222 then (FuturesTradeMessage.decode bytes).map fun (message, rest) => (.futuresTradeMessage message, rest)
  else if tag = 17235 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 17440 then (OptionRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.optionRequestForQuoteRfqMessage message, rest)
  else if tag = 17474 then (FutureOptionsRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.futureOptionsRequestForQuoteRfqMessage message, rest)
  else if tag = 17478 then (FuturesRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.futuresRequestForQuoteRfqMessage message, rest)
  else if tag = 17491 then (StrategyRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.strategyRequestForQuoteRfqMessage message, rest)
  else if tag = 17696 then (InstrumentScheduleNoticeOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeOptionMessage message, rest)
  else if tag = 17730 then (InstrumentScheduleNoticeFuturesOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFuturesOptionMessage message, rest)
  else if tag = 17734 then (InstrumentScheduleNoticeFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFutureMessage message, rest)
  else if tag = 17747 then (InstrumentScheduleNoticeStrategyMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeStrategyMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 17986 then (FutureOptionsQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsQuoteMessage message, rest)
  else if tag = 17990 then (FuturesQuoteMessage.decode bytes).map fun (message, rest) => (.futuresQuoteMessage message, rest)
  else if tag = 18003 then (StrategyQuoteMessage.decode bytes).map fun (message, rest) => (.strategyQuoteMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18498 then (FutureOptionsMarketDepthMessage.decode bytes).map fun (message, rest) => (.futureOptionsMarketDepthMessage message, rest)
  else if tag = 18502 then (FuturesMarketDepthMessage.decode bytes).map fun (message, rest) => (.futuresMarketDepthMessage message, rest)
  else if tag = 18515 then (StrategyMarketDepthMessage.decode bytes).map fun (message, rest) => (.strategyMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18754 then (FutureOptionsTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCancellationMessage message, rest)
  else if tag = 18758 then (FuturesTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futuresTradeCancellationMessage message, rest)
  else if tag = 18771 then (StrategyTradeCancellationMessage.decode bytes).map fun (message, rest) => (.strategyTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19010 then (FutureOptionsInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futureOptionsInstrumentKeysMessage message, rest)
  else if tag = 19013 then (UnderlyingInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.underlyingInstrumentKeysMessage message, rest)
  else if tag = 19014 then (FuturesInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futuresInstrumentKeysMessage message, rest)
  else if tag = 19027 then (StrategyInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.strategyInstrumentKeysMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20034 then (FutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.futureOptionsSummaryMessage message, rest)
  else if tag = 20038 then (FuturesSummaryMessage.decode bytes).map fun (message, rest) => (.futuresSummaryMessage message, rest)
  else if tag = 20051 then (StrategySummaryMessage.decode bytes).map fun (message, rest) => (.strategySummaryMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20802 then (BeginningOfFutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFutureOptionsSummaryMessage message, rest)
  else if tag = 20806 then (BeginningOfFuturesSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFuturesSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfStrategySummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfStrategySummaryMessage message, rest)
  else if tag = 22598 then (FuturesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futuresTradeCorrectionMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (GroupStatusStrategiesMessage.decode bytes).map fun (message, rest) => (.groupStatusStrategiesMessage message, rest)
  else if tag = 19488 then (BulletinsMessage.decode bytes).map fun (message, rest) => (.bulletinsMessage message, rest)
  else if tag = 21280 then (EndOfSalesMessage.decode bytes).map fun (message, rest) => (.endOfSalesMessage message, rest)
  else if tag = 21588 then (TickTableMessage.decode bytes).map fun (message, rest) => (.tickTableMessage message, rest)
  else if tag = 21792 then (EndOfTransmissionMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionMessage message, rest)
  else if tag = 22048 then (CircuitAssuranceMessage.decode bytes).map fun (message, rest) => (.circuitAssuranceMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  hsvfStx : BitVec 8
  sequenceNumber : Alpha 9
  messageBody : MessageBody
  hsvfEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.hsvfStx
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.hsvfEtx))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (hsvfStx, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (hsvfEtx, bytes) ← decodeUInt 1 bytes
  pure ({ hsvfStx, sequenceNumber, messageBody, hsvfEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 3605 := by
  unfold encode
  cases message.messageBody with
  | loginMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LoginMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LogoutMessage.encode_length]
    omega
  | loginAcknowledgementMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LoginAcknowledgementMessage.encode_length]
    omega
  | logoutAcknowledgementMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LogoutAcknowledgementMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionBeginMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionBeginMessage.encode_length]
    omega
  | retransmissionEndMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionEndMessage.encode_length]
    omega
  | errorMessageMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ErrorMessageMessage.encode_length]
    omega
  | optionTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeMessage.encode_length]
    omega
  | optionRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRequestForQuoteRfqMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsRequestForQuoteRfqMessage.encode_length]
    omega
  | futuresRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesRequestForQuoteRfqMessage.encode_length]
    omega
  | strategyRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyRequestForQuoteRfqMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futuresTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategySummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusStrategiesMessage.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfSalesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfTransmissionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CircuitAssuranceMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.TmxMxSolamulticastHsvfV112
