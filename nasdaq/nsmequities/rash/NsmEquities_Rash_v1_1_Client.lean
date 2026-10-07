import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Rash v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesRashAsciirashV11Client

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
  [0x59, 0x4E, 0x41, 0x49, 0x50, 0x57, 0x4C, 0x4F, 0x54, 0x51, 0x4D, 0x42, 0x43, 0x63, 0x64]

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
  | mEloAndContinuousBookMidpoint -- M Elo And Continuous Book Midpoint
  | contraMidpointOnly -- Contra Midpoint Only
  | contraMidpointOnlyPostOnly -- Contra Midpoint Only Post Only
  | directListingCapitalRaise -- Direct Listing Capital Raise
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
  | .mEloAndContinuousBookMidpoint => 0x42
  | .contraMidpointOnly => 0x43
  | .contraMidpointOnlyPostOnly => 0x63
  | .directListingCapitalRaise => 0x64
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
  else if byte = 0x42 then .mEloAndContinuousBookMidpoint
  else if byte = 0x43 then .contraMidpointOnly
  else if byte = 0x63 then .contraMidpointOnlyPostOnly
  else .directListingCapitalRaise

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
  | mEloAndContinuousBookMidpoint => decide
  | contraMidpointOnly => decide
  | contraMidpointOnlyPostOnly => decide
  | directListingCapitalRaise => decide
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

/-- Trade Now: one byte code -/
def TradeNow.codes : List UInt8 :=
  [0x42, 0x4E]

inductive TradeNow where
  | tradeNow -- Trade Now
  | notATradeNow -- Not A Trade Now
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeNow.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeNow

def toByte : TradeNow → UInt8
  | .tradeNow => 0x42
  | .notATradeNow => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeNow :=
  if byte = 0x42 then .tradeNow
  else .notATradeNow

def ofByte (byte : UInt8) : TradeNow :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeNow) : ofByte value.toByte = value := by
  cases value with
  | tradeNow => decide
  | notATradeNow => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeNow) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeNow × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeNow) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeNow) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeNow

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
  [0x4F, 0x43, 0x49, 0x4E, 0x52, 0x45, 0x41]

inductive CrossType where
  | openingCross -- Opening Cross
  | closingCross -- Closing Cross
  | intradayCross -- Intraday Cross
  | immediatelyLive -- Immediately Live
  | retailCross -- Retail Cross
  | extendedLife -- Extended Life
  | extendedTradingClose -- Extended Trading Close
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingCross => 0x4F
  | .closingCross => 0x43
  | .intradayCross => 0x49
  | .immediatelyLive => 0x4E
  | .retailCross => 0x52
  | .extendedLife => 0x45
  | .extendedTradingClose => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openingCross
  else if byte = 0x43 then .closingCross
  else if byte = 0x49 then .intradayCross
  else if byte = 0x4E then .immediatelyLive
  else if byte = 0x52 then .retailCross
  else if byte = 0x45 then .extendedLife
  else .extendedTradingClose

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingCross => decide
  | closingCross => decide
  | intradayCross => decide
  | immediatelyLive => decide
  | retailCross => decide
  | extendedLife => decide
  | extendedTradingClose => decide
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

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65391
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65391 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65391 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequestPacket

/-- Enter Order Message: 140 bytes -/
structure EnterOrderMessage where
  orderTokenClientOrderId : Alpha 14
  side : Side
  sharesOrderQty : Alpha 6
  stockSymbol : Alpha 8
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
  tradeNow : TradeNow
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
    ++ (CustomerType.encode message.customerType
    ++ (TradeNow.encode message.tradeNow))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (side, bytes) ← Side.decode bytes
  let (sharesOrderQty, bytes) ← Alpha.decode 6 bytes
  let (stockSymbol, bytes) ← Alpha.decode 8 bytes
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
  let (tradeNow_, bytes) ← TradeNow.decode bytes
  pure ({ orderTokenClientOrderId, side, sharesOrderQty, stockSymbol, price, timeInForce, firmClientId, display, minQty, maxFloor, pegType, pegDifferenceSign, pegDifference, discretionPrice, discretionPegType, discretionPegDifferenceSign, discretionPegDifference, capacityRule80AIndicator, randomReserve, routeDestExecBroker, custTerminalIdSenderSubId, customerType, tradeNow := tradeNow_ }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessage) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length, PegType.encode_length, PegDifferenceSign.encode_length, DiscretionPegType.encode_length, DiscretionPegDifferenceSign.encode_length, CustomerType.encode_length, TradeNow.encode_length]

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
  rw [List.append_assoc, CustomerType.decode_encode, some_bind]
  dsimp only
  rw [TradeNow.decode_encode, some_bind]
  rfl

end EnterOrderMessage

/-- Enter Order Message With Cross Functionality: 142 bytes -/
structure EnterOrderMessageWithCrossFunctionality where
  orderTokenClientOrderId : Alpha 14
  side : Side
  sharesOrderQty : Alpha 6
  stockSymbol : Alpha 8
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
  tradeNow : TradeNow
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
    ++ (TradeNow.encode message.tradeNow))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EnterOrderMessageWithCrossFunctionality × List UInt8) := do
  let (orderTokenClientOrderId, bytes) ← Alpha.decode 14 bytes
  let (side, bytes) ← Side.decode bytes
  let (sharesOrderQty, bytes) ← Alpha.decode 6 bytes
  let (stockSymbol, bytes) ← Alpha.decode 8 bytes
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
  let (tradeNow_, bytes) ← TradeNow.decode bytes
  pure ({ orderTokenClientOrderId, side, sharesOrderQty, stockSymbol, price, timeInForce, firmClientId, display, minQty, maxFloor, pegType, pegDifferenceSign, pegDifference, discretionPrice, discretionPegType, discretionPegDifferenceSign, discretionPegDifference, capacityRule80AIndicator, randomReserve, routeDestExecBroker, custTerminalIdSenderSubId, intermarketSweepEligibility, crossType, customerType, tradeNow := tradeNow_ }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessageWithCrossFunctionality) : (encode message).length = 142 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length, PegType.encode_length, PegDifferenceSign.encode_length, DiscretionPegType.encode_length, DiscretionPegDifferenceSign.encode_length, IntermarketSweepEligibility.encode_length, CrossType.encode_length, CustomerType.encode_length, TradeNow.encode_length]

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
  rw [TradeNow.decode_encode, some_bind]
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
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 142 := by
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
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 143 := by
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- "R" 0x52
  | logoutRequest (message : LogoutRequest) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 65391 := by
  cases message with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [encode, LogoutRequest.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 76 then (LoginRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 82 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 79 then (LogoutRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutRequest message) else none
  else none

theorem decode_encode (message : ClientPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginRequestPacket message => simp [decode, encode, tag, LoginRequestPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode_nil]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option ClientSoupBinTcpPacket := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let clientPayload ← ClientPayload.decode clientPacketType bytes
  pure { clientPayload }

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length]
    omega
  | clientHeartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LogoutRequest.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNsmequitiesRashAsciirashV11Client
