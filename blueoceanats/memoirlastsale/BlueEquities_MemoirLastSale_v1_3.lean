import Omi.Wire

/-!
# Blue Ocean Technologies Member Order Information Record Last Sale v1.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sbe Message is not framed: its size rule is not the length plus a constant the frame proof covers.

Note: Message's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BlueoceanatsBlueequitiesMemoirlastsaleSbeV13

/-- Security Trading Status: one byte code -/
def SecurityTradingStatus.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive SecurityTradingStatus where
  | halted -- Halted
  | paused -- Paused
  | quoting -- Quoting
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityTradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityTradingStatus

def toByte : SecurityTradingStatus → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quoting => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityTradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quoting
  else .trading

def ofByte (byte : UInt8) : SecurityTradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityTradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quoting => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityTradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityTradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityTradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityTradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityTradingStatus

/-- Security Trading Status Reason: one byte code -/
def SecurityTradingStatusReason.codes : List UInt8 :=
  [0x58, 0x52, 0x41]

inductive SecurityTradingStatusReason where
  | none_ -- None
  | regulatory -- Regulatory
  | administrative -- Administrative
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityTradingStatusReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityTradingStatusReason

def toByte : SecurityTradingStatusReason → UInt8
  | .none_ => 0x58
  | .regulatory => 0x52
  | .administrative => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityTradingStatusReason :=
  if byte = 0x58 then .none_
  else if byte = 0x52 then .regulatory
  else .administrative

def ofByte (byte : UInt8) : SecurityTradingStatusReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityTradingStatusReason) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | regulatory => decide
  | administrative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityTradingStatusReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityTradingStatusReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityTradingStatusReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityTradingStatusReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityTradingStatusReason

/-- Trading Session: one byte code -/
def TradingSession.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive TradingSession where
  | opening -- Opening
  | trading -- Trading
  | postTrading -- Post Trading
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSession.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSession

def toByte : TradingSession → UInt8
  | .opening => 0x31
  | .trading => 0x32
  | .postTrading => 0x33
  | .closed => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSession :=
  if byte = 0x31 then .opening
  else if byte = 0x32 then .trading
  else if byte = 0x33 then .postTrading
  else .closed

def ofByte (byte : UInt8) : TradingSession :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSession) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | trading => decide
  | postTrading => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingSession) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingSession × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingSession) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingSession) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingSession

/-- Sale Condition 1: one byte code -/
def SaleCondition1.codes : List UInt8 :=
  [0x40]

inductive SaleCondition1 where
  | regular -- Regular
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition1

def toByte : SaleCondition1 → UInt8
  | .regular => 0x40
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SaleCondition1 :=
  .regular

def ofByte (byte : UInt8) : SaleCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition1) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition1

/-- Sale Condition 2: one byte code -/
def SaleCondition2.codes : List UInt8 :=
  [0x46, 0x20]

inductive SaleCondition2 where
  | intermarketSweep -- Intermarket Sweep
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition2

def toByte : SaleCondition2 → UInt8
  | .intermarketSweep => 0x46
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition2 :=
  if byte = 0x46 then .intermarketSweep
  else .notApplicable

def ofByte (byte : UInt8) : SaleCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition2) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition2

/-- Sale Condition 3: one byte code -/
def SaleCondition3.codes : List UInt8 :=
  [0x54, 0x20]

inductive SaleCondition3 where
  | formT -- Form T
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition3

def toByte : SaleCondition3 → UInt8
  | .formT => 0x54
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition3 :=
  if byte = 0x54 then .formT
  else .notApplicable

def ofByte (byte : UInt8) : SaleCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition3) : ofByte value.toByte = value := by
  cases value with
  | formT => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition3

/-- Sale Condition 4: one byte code -/
def SaleCondition4.codes : List UInt8 :=
  [0x48, 0x49, 0x58, 0x20]

inductive SaleCondition4 where
  | priceVariation -- Price Variation
  | oddLot -- Odd Lot
  | cross -- Cross
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition4

def toByte : SaleCondition4 → UInt8
  | .priceVariation => 0x48
  | .oddLot => 0x49
  | .cross => 0x58
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition4 :=
  if byte = 0x48 then .priceVariation
  else if byte = 0x49 then .oddLot
  else if byte = 0x58 then .cross
  else .notApplicable

def ofByte (byte : UInt8) : SaleCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition4) : ofByte value.toByte = value := by
  cases value with
  | priceVariation => decide
  | oddLot => decide
  | cross => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition4

/-- Original Sale Condition 1: one byte code -/
def OriginalSaleCondition1.codes : List UInt8 :=
  [0x40]

inductive OriginalSaleCondition1 where
  | regular -- Regular
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition1

def toByte : OriginalSaleCondition1 → UInt8
  | .regular => 0x40
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : OriginalSaleCondition1 :=
  .regular

def ofByte (byte : UInt8) : OriginalSaleCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition1) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSaleCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition1

/-- Original Sale Condition 2: one byte code -/
def OriginalSaleCondition2.codes : List UInt8 :=
  [0x46, 0x20]

inductive OriginalSaleCondition2 where
  | intermarketSweep -- Intermarket Sweep
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition2

def toByte : OriginalSaleCondition2 → UInt8
  | .intermarketSweep => 0x46
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSaleCondition2 :=
  if byte = 0x46 then .intermarketSweep
  else .notApplicable

def ofByte (byte : UInt8) : OriginalSaleCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition2) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSaleCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition2

/-- Original Sale Condition 3: one byte code -/
def OriginalSaleCondition3.codes : List UInt8 :=
  [0x54, 0x20]

inductive OriginalSaleCondition3 where
  | formT -- Form T
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition3

def toByte : OriginalSaleCondition3 → UInt8
  | .formT => 0x54
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSaleCondition3 :=
  if byte = 0x54 then .formT
  else .notApplicable

def ofByte (byte : UInt8) : OriginalSaleCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition3) : ofByte value.toByte = value := by
  cases value with
  | formT => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSaleCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition3

/-- Original Sale Condition 4: one byte code -/
def OriginalSaleCondition4.codes : List UInt8 :=
  [0x48, 0x49, 0x58, 0x20]

inductive OriginalSaleCondition4 where
  | priceVariation -- Price Variation
  | oddLot -- Odd Lot
  | cross -- Cross
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition4

def toByte : OriginalSaleCondition4 → UInt8
  | .priceVariation => 0x48
  | .oddLot => 0x49
  | .cross => 0x58
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSaleCondition4 :=
  if byte = 0x48 then .priceVariation
  else if byte = 0x49 then .oddLot
  else if byte = 0x58 then .cross
  else .notApplicable

def ofByte (byte : UInt8) : OriginalSaleCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition4) : ofByte value.toByte = value := by
  cases value with
  | priceVariation => decide
  | oddLot => decide
  | cross => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OriginalSaleCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition4

/-- Corrected Sale Condition 1: one byte code -/
def CorrectedSaleCondition1.codes : List UInt8 :=
  [0x40]

inductive CorrectedSaleCondition1 where
  | regular -- Regular
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition1

def toByte : CorrectedSaleCondition1 → UInt8
  | .regular => 0x40
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : CorrectedSaleCondition1 :=
  .regular

def ofByte (byte : UInt8) : CorrectedSaleCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition1) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSaleCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition1

/-- Corrected Sale Condition 2: one byte code -/
def CorrectedSaleCondition2.codes : List UInt8 :=
  [0x46, 0x20]

inductive CorrectedSaleCondition2 where
  | intermarketSweep -- Intermarket Sweep
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition2

def toByte : CorrectedSaleCondition2 → UInt8
  | .intermarketSweep => 0x46
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSaleCondition2 :=
  if byte = 0x46 then .intermarketSweep
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedSaleCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition2) : ofByte value.toByte = value := by
  cases value with
  | intermarketSweep => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSaleCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition2

/-- Corrected Sale Condition 3: one byte code -/
def CorrectedSaleCondition3.codes : List UInt8 :=
  [0x54, 0x20]

inductive CorrectedSaleCondition3 where
  | formT -- Form T
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition3

def toByte : CorrectedSaleCondition3 → UInt8
  | .formT => 0x54
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSaleCondition3 :=
  if byte = 0x54 then .formT
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedSaleCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition3) : ofByte value.toByte = value := by
  cases value with
  | formT => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSaleCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition3

/-- Corrected Sale Condition 4: one byte code -/
def CorrectedSaleCondition4.codes : List UInt8 :=
  [0x48, 0x49, 0x58, 0x20]

inductive CorrectedSaleCondition4 where
  | priceVariation -- Price Variation
  | oddLot -- Odd Lot
  | cross -- Cross
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition4

def toByte : CorrectedSaleCondition4 → UInt8
  | .priceVariation => 0x48
  | .oddLot => 0x49
  | .cross => 0x58
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSaleCondition4 :=
  if byte = 0x48 then .priceVariation
  else if byte = 0x49 then .oddLot
  else if byte = 0x58 then .cross
  else .notApplicable

def ofByte (byte : UInt8) : CorrectedSaleCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition4) : ofByte value.toByte = value := by
  cases value with
  | priceVariation => decide
  | oddLot => decide
  | cross => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CorrectedSaleCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition4

/-- Instrument Directory Message: 35 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  roundLot : BitVec 32
  isTestSymbol : BitVec 8
  mpv : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (encodeUInt 4 message.roundLot
    ++ (encodeUInt 1 message.isTestSymbol
    ++ (encodeUInt 8 message.mpv))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (roundLot, bytes) ← decodeUInt 4 bytes
  let (isTestSymbol, bytes) ← decodeUInt 1 bytes
  let (mpv, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, symbol, symbolSfx, roundLot, isTestSymbol, mpv }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Reg Sho Restriction Message: 11 bytes -/
structure RegShoRestrictionMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  shortSaleRestriction : BitVec 8
  deriving DecidableEq, Repr

namespace RegShoRestrictionMessage

def encode (message : RegShoRestrictionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 1 message.shortSaleRestriction))

def decode (bytes : List UInt8) : Option (RegShoRestrictionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (shortSaleRestriction, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, securityId, shortSaleRestriction }, bytes)

@[simp] theorem encode_length (message : RegShoRestrictionMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RegShoRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RegShoRestrictionMessage

/-- Security Trading Status Message: 12 bytes -/
structure SecurityTradingStatusMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  securityTradingStatus : SecurityTradingStatus
  securityTradingStatusReason : SecurityTradingStatusReason
  deriving DecidableEq, Repr

namespace SecurityTradingStatusMessage

def encode (message : SecurityTradingStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (SecurityTradingStatus.encode message.securityTradingStatus
    ++ (SecurityTradingStatusReason.encode message.securityTradingStatusReason)))

def decode (bytes : List UInt8) : Option (SecurityTradingStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (securityTradingStatus, bytes) ← SecurityTradingStatus.decode bytes
  let (securityTradingStatusReason, bytes) ← SecurityTradingStatusReason.decode bytes
  pure ({ timestamp, securityId, securityTradingStatus, securityTradingStatusReason }, bytes)

@[simp] theorem encode_length (message : SecurityTradingStatusMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SecurityTradingStatus.encode_length, SecurityTradingStatusReason.encode_length]

theorem encode_length_pos (message : SecurityTradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityTradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [SecurityTradingStatusReason.decode_encode, some_bind]
  rfl

end SecurityTradingStatusMessage

/-- Trading Session Status Message: 9 bytes -/
structure TradingSessionStatusMessage where
  timestamp : BitVec 64
  tradingSession : TradingSession
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (TradingSession.encode message.tradingSession)

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (tradingSession, bytes) ← TradingSession.decode bytes
  pure ({ timestamp, tradingSession }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingSession.encode_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradingSession.decode_encode, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Trade Report Message: 34 bytes -/
structure TradeReportMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  tradeQty : BitVec 32
  tradePrice : BitVec 64
  saleCondition1 : SaleCondition1
  saleCondition2 : SaleCondition2
  saleCondition3 : SaleCondition3
  saleCondition4 : SaleCondition4
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.tradeQty
    ++ (encodeUInt 8 message.tradePrice
    ++ (SaleCondition1.encode message.saleCondition1
    ++ (SaleCondition2.encode message.saleCondition2
    ++ (SaleCondition3.encode message.saleCondition3
    ++ (SaleCondition4.encode message.saleCondition4))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradeQty, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (saleCondition1, bytes) ← SaleCondition1.decode bytes
  let (saleCondition2, bytes) ← SaleCondition2.decode bytes
  let (saleCondition3, bytes) ← SaleCondition3.decode bytes
  let (saleCondition4, bytes) ← SaleCondition4.decode bytes
  pure ({ timestamp, securityId, tradeId, tradeQty, tradePrice, saleCondition1, saleCondition2, saleCondition3, saleCondition4 }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SaleCondition1.encode_length, SaleCondition2.encode_length, SaleCondition3.encode_length, SaleCondition4.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [SaleCondition4.decode_encode, some_bind]
  rfl

end TradeReportMessage

/-- Trade Cancel Message: 34 bytes -/
structure TradeCancelMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  tradeQty : BitVec 32
  lastPrice : BitVec 64
  saleCondition1 : SaleCondition1
  saleCondition2 : SaleCondition2
  saleCondition3 : SaleCondition3
  saleCondition4 : SaleCondition4
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.tradeQty
    ++ (encodeUInt 8 message.lastPrice
    ++ (SaleCondition1.encode message.saleCondition1
    ++ (SaleCondition2.encode message.saleCondition2
    ++ (SaleCondition3.encode message.saleCondition3
    ++ (SaleCondition4.encode message.saleCondition4))))))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradeQty, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (saleCondition1, bytes) ← SaleCondition1.decode bytes
  let (saleCondition2, bytes) ← SaleCondition2.decode bytes
  let (saleCondition3, bytes) ← SaleCondition3.decode bytes
  let (saleCondition4, bytes) ← SaleCondition4.decode bytes
  pure ({ timestamp, securityId, tradeId, tradeQty, lastPrice, saleCondition1, saleCondition2, saleCondition3, saleCondition4 }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SaleCondition1.encode_length, SaleCondition2.encode_length, SaleCondition3.encode_length, SaleCondition4.encode_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [SaleCondition4.decode_encode, some_bind]
  rfl

end TradeCancelMessage

/-- Trade Correct Message: 50 bytes -/
structure TradeCorrectMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  originalTradeQty : BitVec 32
  originalTradePrice : BitVec 64
  originalSaleCondition1 : OriginalSaleCondition1
  originalSaleCondition2 : OriginalSaleCondition2
  originalSaleCondition3 : OriginalSaleCondition3
  originalSaleCondition4 : OriginalSaleCondition4
  correctedTradeQty : BitVec 32
  correctedTradePrice : BitVec 64
  correctedSaleCondition1 : CorrectedSaleCondition1
  correctedSaleCondition2 : CorrectedSaleCondition2
  correctedSaleCondition3 : CorrectedSaleCondition3
  correctedSaleCondition4 : CorrectedSaleCondition4
  deriving DecidableEq, Repr

namespace TradeCorrectMessage

def encode (message : TradeCorrectMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalTradeQty
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (OriginalSaleCondition1.encode message.originalSaleCondition1
    ++ (OriginalSaleCondition2.encode message.originalSaleCondition2
    ++ (OriginalSaleCondition3.encode message.originalSaleCondition3
    ++ (OriginalSaleCondition4.encode message.originalSaleCondition4
    ++ (encodeUInt 4 message.correctedTradeQty
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (CorrectedSaleCondition1.encode message.correctedSaleCondition1
    ++ (CorrectedSaleCondition2.encode message.correctedSaleCondition2
    ++ (CorrectedSaleCondition3.encode message.correctedSaleCondition3
    ++ (CorrectedSaleCondition4.encode message.correctedSaleCondition4))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalTradeQty, bytes) ← decodeUInt 4 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalSaleCondition1, bytes) ← OriginalSaleCondition1.decode bytes
  let (originalSaleCondition2, bytes) ← OriginalSaleCondition2.decode bytes
  let (originalSaleCondition3, bytes) ← OriginalSaleCondition3.decode bytes
  let (originalSaleCondition4, bytes) ← OriginalSaleCondition4.decode bytes
  let (correctedTradeQty, bytes) ← decodeUInt 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedSaleCondition1, bytes) ← CorrectedSaleCondition1.decode bytes
  let (correctedSaleCondition2, bytes) ← CorrectedSaleCondition2.decode bytes
  let (correctedSaleCondition3, bytes) ← CorrectedSaleCondition3.decode bytes
  let (correctedSaleCondition4, bytes) ← CorrectedSaleCondition4.decode bytes
  pure ({ timestamp, securityId, tradeId, originalTradeQty, originalTradePrice, originalSaleCondition1, originalSaleCondition2, originalSaleCondition3, originalSaleCondition4, correctedTradeQty, correctedTradePrice, correctedSaleCondition1, correctedSaleCondition2, correctedSaleCondition3, correctedSaleCondition4 }, bytes)

@[simp] theorem encode_length (message : TradeCorrectMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginalSaleCondition1.encode_length, OriginalSaleCondition2.encode_length, OriginalSaleCondition3.encode_length, OriginalSaleCondition4.encode_length, CorrectedSaleCondition1.encode_length, CorrectedSaleCondition2.encode_length, CorrectedSaleCondition3.encode_length, CorrectedSaleCondition4.encode_length]

theorem encode_length_pos (message : TradeCorrectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [CorrectedSaleCondition4.decode_encode, some_bind]
  rfl

end TradeCorrectMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 1
  | regShoRestrictionMessage (message : RegShoRestrictionMessage) -- 2
  | securityTradingStatusMessage (message : SecurityTradingStatusMessage) -- 3
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 5
  | tradeReportMessage (message : TradeReportMessage) -- 10
  | tradeCancelMessage (message : TradeCancelMessage) -- 11
  | tradeCorrectMessage (message : TradeCorrectMessage) -- 12
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .instrumentDirectoryMessage _ => 1
  | .regShoRestrictionMessage _ => 2
  | .securityTradingStatusMessage _ => 3
  | .tradingSessionStatusMessage _ => 5
  | .tradeReportMessage _ => 10
  | .tradeCancelMessage _ => 11
  | .tradeCorrectMessage _ => 12

def encode : Payload → List UInt8
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .regShoRestrictionMessage message => RegShoRestrictionMessage.encode message
  | .securityTradingStatusMessage message => SecurityTradingStatusMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .tradeCorrectMessage message => TradeCorrectMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 50 := by
  cases message with
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [encode, RegShoRestrictionMessage.encode_length]
    omega
  | securityTradingStatusMessage inner =>
    simp only [encode, SecurityTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega
  | tradeCorrectMessage inner =>
    simp only [encode, TradeCorrectMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 2 then (RegShoRestrictionMessage.decode bytes).map fun (message, rest) => (.regShoRestrictionMessage message, rest)
  else if tag = 3 then (SecurityTradingStatusMessage.decode bytes).map fun (message, rest) => (.securityTradingStatusMessage message, rest)
  else if tag = 5 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 10 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 11 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else if tag = 12 then (TradeCorrectMessage.decode bytes).map fun (message, rest) => (.tradeCorrectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 56 := by
  unfold encode
  cases message.payload with
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RegShoRestrictionMessage.encode_length]
    omega
  | securityTradingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SecurityTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCancelMessage.encode_length]
    omega
  | tradeCorrectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeCorrectMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Message -/
structure Message where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [SbeMessage.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Message

/-- Sequenced Message -/
structure SequencedMessage where
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (SequencedMessage × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : SequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end SequencedMessage

/-- Any Sequenced Messages, selected by Message Type -/
inductive SequencedMessages where
  | sequencedMessage (message : SequencedMessage) -- 2
  deriving DecidableEq, Repr

namespace SequencedMessages

/-- The Message Type each message is sent under -/
def tag : SequencedMessages → BitVec 8
  | .sequencedMessage _ => 2

def encode : SequencedMessages → List UInt8
  | .sequencedMessage message => SequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessages × List UInt8) :=
  if tag = 2 then (SequencedMessage.decode bytes).map fun (message, rest) => (.sequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessages) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessages

/-- Packet -/
structure Packet where
  headerLength : BitVec 8
  sessionId : BitVec 64
  sequenceNumber : BitVec 64
  sequencedMessages : SequencedMessages
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (SequencedMessages.tag message.sequencedMessages)
    ++ (encodeUInt 1 message.headerLength
    ++ (encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (SequencedMessages.encode message.sequencedMessages))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (headerLength, bytes) ← decodeUInt 1 bytes
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (sequencedMessages, bytes) ← SequencedMessages.decode messageType bytes
  pure ({ headerLength, sessionId, sequenceNumber, sequencedMessages }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessages.decode_encode, some_bind]
  rfl

end Packet

end Omi.BlueoceanatsBlueequitiesMemoirlastsaleSbeV13
