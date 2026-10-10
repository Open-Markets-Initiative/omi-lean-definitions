import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Rash v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesRashAsciirashV10Client

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | short -- Short
  | shortExempt -- Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .short => 0x54
  | .shortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .short
  else .shortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | short => decide
  | shortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x59, 0x4E, 0x41, 0x49, 0x50, 0x57, 0x4C, 0x4F, 0x54, 0x51, 0x4D, 0x6D, 0x6E, 0x42]

inductive Display where
  | anonymousPriceToComply -- Anonymous Price To Comply
  | nonDisplayed -- Non Displayed
  | attributablePriceToDisplay -- Attributable Price To Display
  | imbalanceOnly -- Imbalance Only
  | postOnly -- Post Only
  | midPointPegPostOnly -- Mid Point Peg Post Only
  | postOnlyAndAttributablePriceToDisplay -- Post Only And Attributable Price To Display
  | retailOrderType1 -- Retail Order Type 1
  | retailOrderType2 -- Retail Order Type 2
  | retailPriceImprovementOrder -- Retail Price Improvement Order
  | midPointPeg -- Mid Point Peg
  | midPointPegAndMidPointTradeNow -- Mid Point Peg And Mid Point Trade Now
  | nonDisplayAndMidPointTradeNow -- Non Display And Mid Point Trade Now
  | mEloAndContinuousBookMidpoint -- M Elo And Continuous Book Midpoint
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .anonymousPriceToComply => 0x59
  | .nonDisplayed => 0x4E
  | .attributablePriceToDisplay => 0x41
  | .imbalanceOnly => 0x49
  | .postOnly => 0x50
  | .midPointPegPostOnly => 0x57
  | .postOnlyAndAttributablePriceToDisplay => 0x4C
  | .retailOrderType1 => 0x4F
  | .retailOrderType2 => 0x54
  | .retailPriceImprovementOrder => 0x51
  | .midPointPeg => 0x4D
  | .midPointPegAndMidPointTradeNow => 0x6D
  | .nonDisplayAndMidPointTradeNow => 0x6E
  | .mEloAndContinuousBookMidpoint => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x59 then .anonymousPriceToComply
  else if byte = 0x4E then .nonDisplayed
  else if byte = 0x41 then .attributablePriceToDisplay
  else if byte = 0x49 then .imbalanceOnly
  else if byte = 0x50 then .postOnly
  else if byte = 0x57 then .midPointPegPostOnly
  else if byte = 0x4C then .postOnlyAndAttributablePriceToDisplay
  else if byte = 0x4F then .retailOrderType1
  else if byte = 0x54 then .retailOrderType2
  else if byte = 0x51 then .retailPriceImprovementOrder
  else if byte = 0x4D then .midPointPeg
  else if byte = 0x6D then .midPointPegAndMidPointTradeNow
  else if byte = 0x6E then .nonDisplayAndMidPointTradeNow
  else .mEloAndContinuousBookMidpoint

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | anonymousPriceToComply => decide
  | nonDisplayed => decide
  | attributablePriceToDisplay => decide
  | imbalanceOnly => decide
  | postOnly => decide
  | midPointPegPostOnly => decide
  | postOnlyAndAttributablePriceToDisplay => decide
  | retailOrderType1 => decide
  | retailOrderType2 => decide
  | retailPriceImprovementOrder => decide
  | midPointPeg => decide
  | midPointPegAndMidPointTradeNow => decide
  | nonDisplayAndMidPointTradeNow => decide
  | mEloAndContinuousBookMidpoint => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Peg Type: one byte code -/
def PegType.codes : List UInt8 :=
  [0x4D, 0x4E, 0x50, 0x52, 0x51, 0x49]

inductive PegType where
  | midpoint -- Midpoint
  | noPeg -- No Peg
  | market -- Market
  | primary -- Primary
  | marketMakerPeg -- Market Maker Peg
  | inavPeg -- Inav Peg
  | unlisted (byte : { byte : UInt8 // byte ∉ PegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegType

def toByte : PegType → UInt8
  | .midpoint => 0x4D
  | .noPeg => 0x4E
  | .market => 0x50
  | .primary => 0x52
  | .marketMakerPeg => 0x51
  | .inavPeg => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegType :=
  if byte = 0x4D then .midpoint
  else if byte = 0x4E then .noPeg
  else if byte = 0x50 then .market
  else if byte = 0x52 then .primary
  else if byte = 0x51 then .marketMakerPeg
  else .inavPeg

def ofByte (byte : UInt8) : PegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegType) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | noPeg => decide
  | market => decide
  | primary => decide
  | marketMakerPeg => decide
  | inavPeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegType

/-- Peg Difference Sign: one byte code -/
def PegDifferenceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive PegDifferenceSign where
  | plus -- Plus
  | minus -- Minus
  | unlisted (byte : { byte : UInt8 // byte ∉ PegDifferenceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegDifferenceSign

def toByte : PegDifferenceSign → UInt8
  | .plus => 0x2B
  | .minus => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegDifferenceSign :=
  if byte = 0x2B then .plus
  else .minus

def ofByte (byte : UInt8) : PegDifferenceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegDifferenceSign) : ofByte value.toByte = value := by
  cases value with
  | plus => decide
  | minus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegDifferenceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegDifferenceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegDifferenceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegDifferenceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegDifferenceSign

/-- Discretion Peg Type: one byte code -/
def DiscretionPegType.codes : List UInt8 :=
  [0x4D, 0x4E, 0x50, 0x52, 0x49]

inductive DiscretionPegType where
  | midpoint -- Midpoint
  | noPeg -- No Peg
  | market -- Market
  | primary -- Primary
  | inavPeg -- Inav Peg
  | unlisted (byte : { byte : UInt8 // byte ∉ DiscretionPegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DiscretionPegType

def toByte : DiscretionPegType → UInt8
  | .midpoint => 0x4D
  | .noPeg => 0x4E
  | .market => 0x50
  | .primary => 0x52
  | .inavPeg => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DiscretionPegType :=
  if byte = 0x4D then .midpoint
  else if byte = 0x4E then .noPeg
  else if byte = 0x50 then .market
  else if byte = 0x52 then .primary
  else .inavPeg

def ofByte (byte : UInt8) : DiscretionPegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DiscretionPegType) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | noPeg => decide
  | market => decide
  | primary => decide
  | inavPeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DiscretionPegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DiscretionPegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DiscretionPegType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DiscretionPegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DiscretionPegType

/-- Discretion Peg Difference Sign: one byte code -/
def DiscretionPegDifferenceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive DiscretionPegDifferenceSign where
  | plus -- Plus
  | minus -- Minus
  | unlisted (byte : { byte : UInt8 // byte ∉ DiscretionPegDifferenceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DiscretionPegDifferenceSign

def toByte : DiscretionPegDifferenceSign → UInt8
  | .plus => 0x2B
  | .minus => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DiscretionPegDifferenceSign :=
  if byte = 0x2B then .plus
  else .minus

def ofByte (byte : UInt8) : DiscretionPegDifferenceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DiscretionPegDifferenceSign) : ofByte value.toByte = value := by
  cases value with
  | plus => decide
  | minus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DiscretionPegDifferenceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DiscretionPegDifferenceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DiscretionPegDifferenceSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DiscretionPegDifferenceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DiscretionPegDifferenceSign

/-- Customer Type: one byte code -/
def CustomerType.codes : List UInt8 :=
  [0x52, 0x4E]

inductive CustomerType where
  | retailDesignatedOrder -- Retail Designated Order
  | notARetailDesignatedOrder -- Not A Retail Designated Order
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerType

def toByte : CustomerType → UInt8
  | .retailDesignatedOrder => 0x52
  | .notARetailDesignatedOrder => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustomerType :=
  if byte = 0x52 then .retailDesignatedOrder
  else .notARetailDesignatedOrder

def ofByte (byte : UInt8) : CustomerType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerType) : ofByte value.toByte = value := by
  cases value with
  | retailDesignatedOrder => decide
  | notARetailDesignatedOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustomerType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerType

/-- Intermarket Sweep Eligibility: one byte code -/
def IntermarketSweepEligibility.codes : List UInt8 :=
  [0x59, 0x4E, 0x79]

inductive IntermarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | tradeAtIntermarketSweepOrder -- Trade At Intermarket Sweep Order
  | unlisted (byte : { byte : UInt8 // byte ∉ IntermarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IntermarketSweepEligibility

def toByte : IntermarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .tradeAtIntermarketSweepOrder => 0x79
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IntermarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else if byte = 0x4E then .notEligible
  else .tradeAtIntermarketSweepOrder

def ofByte (byte : UInt8) : IntermarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IntermarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
  | tradeAtIntermarketSweepOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IntermarketSweepEligibility) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IntermarketSweepEligibility × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IntermarketSweepEligibility) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IntermarketSweepEligibility) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IntermarketSweepEligibility

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x43, 0x4E, 0x52, 0x45]

inductive CrossType where
  | openingCross -- Opening Cross
  | closingCross -- Closing Cross
  | immediatelyLive -- Immediately Live
  | retailCross -- Retail Cross
  | extendedLife -- Extended Life
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingCross => 0x4F
  | .closingCross => 0x43
  | .immediatelyLive => 0x4E
  | .retailCross => 0x52
  | .extendedLife => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openingCross
  else if byte = 0x43 then .closingCross
  else if byte = 0x4E then .immediatelyLive
  else if byte = 0x52 then .retailCross
  else .extendedLife

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingCross => decide
  | closingCross => decide
  | immediatelyLive => decide
  | retailCross => decide
  | extendedLife => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Reactive Trade Now: one byte code -/
def ReactiveTradeNow.codes : List UInt8 :=
  [0x42, 0x4E]

inductive ReactiveTradeNow where
  | reactiveTradeNow -- Reactive Trade Now
  | notAReactiveTradeNow -- Not A Reactive Trade Now
  | unlisted (byte : { byte : UInt8 // byte ∉ ReactiveTradeNow.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReactiveTradeNow

def toByte : ReactiveTradeNow → UInt8
  | .reactiveTradeNow => 0x42
  | .notAReactiveTradeNow => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReactiveTradeNow :=
  if byte = 0x42 then .reactiveTradeNow
  else .notAReactiveTradeNow

def ofByte (byte : UInt8) : ReactiveTradeNow :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReactiveTradeNow) : ofByte value.toByte = value := by
  cases value with
  | reactiveTradeNow => decide
  | notAReactiveTradeNow => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReactiveTradeNow) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReactiveTradeNow × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReactiveTradeNow) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReactiveTradeNow) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReactiveTradeNow

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
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

end LoginRequestPacket

/-- Enter Order Message: 137 bytes -/
structure EnterOrderMessage where
  orderTokenClientOrderId : Alpha 14
  side : Side
  sharesOrderQty : Alpha 6
  stockSymbol : Alpha 6
  price : Alpha 10
  timeInForce : Alpha 5
  firmClientId : Alpha 4
  display : Display
  minQty : Alpha 6
  maxFloor : Alpha 6
  pegType : PegType
  pegDifferenceSign : PegDifferenceSign
  pegDifference : Alpha 10
  discretionPrice : Alpha 10
  discretionPegType : DiscretionPegType
  discretionPegDifferenceSign : DiscretionPegDifferenceSign
  discretionPegDifference : Alpha 10
  capacityRule80AIndicator : Alpha 1
  randomReserve : Alpha 6
  routeDestExecBroker : Alpha 4
  custTerminalIdSenderSubId : Alpha 32
  customerType : CustomerType
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.sharesOrderQty
    ++ (Alpha.encode message.stockSymbol
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.firmClientId
    ++ (Display.encode message.display
    ++ (Alpha.encode message.minQty
    ++ (Alpha.encode message.maxFloor
    ++ (PegType.encode message.pegType
    ++ (PegDifferenceSign.encode message.pegDifferenceSign
    ++ (Alpha.encode message.pegDifference
    ++ (Alpha.encode message.discretionPrice
    ++ (DiscretionPegType.encode message.discretionPegType
    ++ (DiscretionPegDifferenceSign.encode message.discretionPegDifferenceSign
    ++ (Alpha.encode message.discretionPegDifference
    ++ (Alpha.encode message.capacityRule80AIndicator
    ++ (Alpha.encode message.randomReserve
    ++ (Alpha.encode message.routeDestExecBroker
    ++ (Alpha.encode message.custTerminalIdSenderSubId
    ++ (CustomerType.encode message.customerType)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (side, bytes) ← Side.decode bytes
  let (sharesOrderQty, bytes) ← Alpha.decode 6 bytes
  let (stockSymbol, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (timeInForce, bytes) ← Alpha.decode 5 bytes
  let (firmClientId, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (minQty, bytes) ← Alpha.decode 6 bytes
  let (maxFloor, bytes) ← Alpha.decode 6 bytes
  let (pegType, bytes) ← PegType.decode bytes
  let (pegDifferenceSign, bytes) ← PegDifferenceSign.decode bytes
  let (pegDifference, bytes) ← Alpha.decode 10 bytes
  let (discretionPrice, bytes) ← Alpha.decode 10 bytes
  let (discretionPegType, bytes) ← DiscretionPegType.decode bytes
  let (discretionPegDifferenceSign, bytes) ← DiscretionPegDifferenceSign.decode bytes
  let (discretionPegDifference, bytes) ← Alpha.decode 10 bytes
  let (capacityRule80AIndicator, bytes) ← Alpha.decode 1 bytes
  let (randomReserve, bytes) ← Alpha.decode 6 bytes
  let (routeDestExecBroker, bytes) ← Alpha.decode 4 bytes
  let (custTerminalIdSenderSubId, bytes) ← Alpha.decode 32 bytes
  let (customerType, bytes) ← CustomerType.decode bytes
  pure ({ orderTokenClientOrderId, side, sharesOrderQty, stockSymbol, price, timeInForce, firmClientId, display, minQty, maxFloor, pegType, pegDifferenceSign, pegDifference, discretionPrice, discretionPegType, discretionPegDifferenceSign, discretionPegDifference, capacityRule80AIndicator, randomReserve, routeDestExecBroker, custTerminalIdSenderSubId, customerType }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessage) : (encode message).length = 137 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length, PegType.encode_length, PegDifferenceSign.encode_length, DiscretionPegType.encode_length, DiscretionPegDifferenceSign.encode_length, CustomerType.encode_length]

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegDifferenceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegDifferenceSign.decode_encode, some_bind]
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
  rw [CustomerType.decode_encode, some_bind]
  rfl

end EnterOrderMessage

/-- Enter Order Message With Cross Functionality: 140 bytes -/
structure EnterOrderMessageWithCrossFunctionality where
  orderTokenClientOrderId : Alpha 14
  side : Side
  sharesOrderQty : Alpha 6
  stockSymbol : Alpha 6
  price : Alpha 10
  timeInForce : Alpha 5
  firmClientId : Alpha 4
  display : Display
  minQty : Alpha 6
  maxFloor : Alpha 6
  pegType : PegType
  pegDifferenceSign : PegDifferenceSign
  pegDifference : Alpha 10
  discretionPrice : Alpha 10
  discretionPegType : DiscretionPegType
  discretionPegDifferenceSign : DiscretionPegDifferenceSign
  discretionPegDifference : Alpha 10
  capacityRule80AIndicator : Alpha 1
  randomReserve : Alpha 6
  routeDestExecBroker : Alpha 4
  custTerminalIdSenderSubId : Alpha 32
  intermarketSweepEligibility : IntermarketSweepEligibility
  crossType : CrossType
  customerType : CustomerType
  reactiveTradeNow : ReactiveTradeNow
  deriving DecidableEq, Repr

namespace EnterOrderMessageWithCrossFunctionality

def encode (message : EnterOrderMessageWithCrossFunctionality) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.sharesOrderQty
    ++ (Alpha.encode message.stockSymbol
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.timeInForce
    ++ (Alpha.encode message.firmClientId
    ++ (Display.encode message.display
    ++ (Alpha.encode message.minQty
    ++ (Alpha.encode message.maxFloor
    ++ (PegType.encode message.pegType
    ++ (PegDifferenceSign.encode message.pegDifferenceSign
    ++ (Alpha.encode message.pegDifference
    ++ (Alpha.encode message.discretionPrice
    ++ (DiscretionPegType.encode message.discretionPegType
    ++ (DiscretionPegDifferenceSign.encode message.discretionPegDifferenceSign
    ++ (Alpha.encode message.discretionPegDifference
    ++ (Alpha.encode message.capacityRule80AIndicator
    ++ (Alpha.encode message.randomReserve
    ++ (Alpha.encode message.routeDestExecBroker
    ++ (Alpha.encode message.custTerminalIdSenderSubId
    ++ (IntermarketSweepEligibility.encode message.intermarketSweepEligibility
    ++ (CrossType.encode message.crossType
    ++ (CustomerType.encode message.customerType
    ++ (ReactiveTradeNow.encode message.reactiveTradeNow))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EnterOrderMessageWithCrossFunctionality × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (side, bytes) ← Side.decode bytes
  let (sharesOrderQty, bytes) ← Alpha.decode 6 bytes
  let (stockSymbol, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (timeInForce, bytes) ← Alpha.decode 5 bytes
  let (firmClientId, bytes) ← Alpha.decode 4 bytes
  let (display, bytes) ← Display.decode bytes
  let (minQty, bytes) ← Alpha.decode 6 bytes
  let (maxFloor, bytes) ← Alpha.decode 6 bytes
  let (pegType, bytes) ← PegType.decode bytes
  let (pegDifferenceSign, bytes) ← PegDifferenceSign.decode bytes
  let (pegDifference, bytes) ← Alpha.decode 10 bytes
  let (discretionPrice, bytes) ← Alpha.decode 10 bytes
  let (discretionPegType, bytes) ← DiscretionPegType.decode bytes
  let (discretionPegDifferenceSign, bytes) ← DiscretionPegDifferenceSign.decode bytes
  let (discretionPegDifference, bytes) ← Alpha.decode 10 bytes
  let (capacityRule80AIndicator, bytes) ← Alpha.decode 1 bytes
  let (randomReserve, bytes) ← Alpha.decode 6 bytes
  let (routeDestExecBroker, bytes) ← Alpha.decode 4 bytes
  let (custTerminalIdSenderSubId, bytes) ← Alpha.decode 32 bytes
  let (intermarketSweepEligibility, bytes) ← IntermarketSweepEligibility.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (customerType, bytes) ← CustomerType.decode bytes
  let (reactiveTradeNow_, bytes) ← ReactiveTradeNow.decode bytes
  pure ({ orderTokenClientOrderId, side, sharesOrderQty, stockSymbol, price, timeInForce, firmClientId, display, minQty, maxFloor, pegType, pegDifferenceSign, pegDifference, discretionPrice, discretionPegType, discretionPegDifferenceSign, discretionPegDifference, capacityRule80AIndicator, randomReserve, routeDestExecBroker, custTerminalIdSenderSubId, intermarketSweepEligibility, crossType, customerType, reactiveTradeNow := reactiveTradeNow_ }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessageWithCrossFunctionality) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length, PegType.encode_length, PegDifferenceSign.encode_length, DiscretionPegType.encode_length, DiscretionPegDifferenceSign.encode_length, IntermarketSweepEligibility.encode_length, CrossType.encode_length, CustomerType.encode_length, ReactiveTradeNow.encode_length]

theorem encode_length_pos (message : EnterOrderMessageWithCrossFunctionality) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EnterOrderMessageWithCrossFunctionality) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PegDifferenceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DiscretionPegDifferenceSign.decode_encode, some_bind]
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
  rw [List.append_assoc, IntermarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerType.decode_encode, some_bind]
  dsimp only
  rw [ReactiveTradeNow.decode_encode, some_bind]
  rfl

end EnterOrderMessageWithCrossFunctionality

/-- Cancel Order Message: 20 bytes -/
structure CancelOrderMessage where
  orderTokenClientOrderId : Alpha 14
  shares : Alpha 6
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  Alpha.encode message.orderTokenClientOrderId
    ++ (Alpha.encode message.shares)

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  pure ({ orderTokenClientOrderId, shares }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- "O" 0x4F
  | enterOrderMessageWithCrossFunctionality (message : EnterOrderMessageWithCrossFunctionality) -- "Q" 0x51
  | cancelOrderMessage (message : CancelOrderMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .enterOrderMessageWithCrossFunctionality _ => 81
  | .cancelOrderMessage _ => 88

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .enterOrderMessageWithCrossFunctionality message => EnterOrderMessageWithCrossFunctionality.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 140 := by
  cases message with
  | enterOrderMessage inner =>
    simp only [encode, EnterOrderMessage.encode_length]
    omega
  | enterOrderMessageWithCrossFunctionality inner =>
    simp only [encode, EnterOrderMessageWithCrossFunctionality.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrderMessage.decode bytes).map fun (message, rest) => (.enterOrderMessage message, rest)
  else if tag = 81 then (EnterOrderMessageWithCrossFunctionality.decode bytes).map fun (message, rest) => (.enterOrderMessageWithCrossFunctionality message, rest)
  else if tag = 88 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 141 := by
  unfold encode
  cases message.unsequencedMessage with
  | enterOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterOrderMessage.encode_length]
    omega
  | enterOrderMessageWithCrossFunctionality inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterOrderMessageWithCrossFunctionality.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 141 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Frame -/
structure ClientFrame where
  clientPayload : ClientPayload
  soupLf : BitVec 8
  deriving DecidableEq, Repr

namespace ClientFrame

def encode (message : ClientFrame) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload
    ++ (encodeUInt 1 message.soupLf))

def decode (bytes : List UInt8) : Option (ClientFrame × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  let (soupLf, bytes) ← decodeUInt 1 bytes
  pure ({ clientPayload, soupLf }, bytes)

theorem encode_length_pos (message : ClientFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientFrame) : (encode message).length ≤ 143 := by
  unfold encode
  cases message.clientPayload with
  | debugPacket inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : ClientFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ClientPayload.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClientFrame

/-- Client Packet -/
structure ClientPacket where
  clientFrame : List ClientFrame
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientFrame.encode message.clientFrame

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientFrame ← decodeAll ClientFrame.decode bytes.length bytes
  pure { clientFrame }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientFrame.encode ClientFrame.decode ClientFrame.decode_encode ClientFrame.encode_length_pos message.clientFrame _ (encodeMany_length_ge ClientFrame.encode ClientFrame.encode_length_pos message.clientFrame), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNsmequitiesRashAsciirashV10Client
