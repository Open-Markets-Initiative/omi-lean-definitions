import Omi.Wire

/-!
# Australian Securities Exchange New Trading Platform v1.05

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AsxAsxderivativesNtpItchV105

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x43]

inductive EventCode where
  | businessTradeDateHasEnded -- Business Trade Date Has Ended
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .businessTradeDateHasEnded => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : EventCode :=
  .businessTradeDateHasEnded

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | businessTradeDateHasEnded => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x50, 0x43]

inductive OptionType where
  | put -- Put
  | call -- Call
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .put => 0x50
  | .call => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x50 then .put
  else .call

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | put => decide
  | call => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Side Leg: one byte code -/
def SideLeg.codes : List UInt8 :=
  [0x42, 0x53]

inductive SideLeg where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ SideLeg.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideLeg

def toByte : SideLeg → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideLeg :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : SideLeg :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideLeg) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SideLeg) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SideLeg × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SideLeg) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SideLeg) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SideLeg

/-- Session State: one byte code -/
def SessionState.codes : List UInt8 :=
  [0x50, 0x4F, 0x52, 0x48, 0x43, 0x4D]

inductive SessionState where
  | preOpen -- Pre Open
  | opened -- Opened
  | regulatoryHalt -- Regulatory Halt
  | halted -- Halted
  | closed -- Closed
  | maintenance -- Maintenance
  | unlisted (byte : { byte : UInt8 // byte ∉ SessionState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SessionState

def toByte : SessionState → UInt8
  | .preOpen => 0x50
  | .opened => 0x4F
  | .regulatoryHalt => 0x52
  | .halted => 0x48
  | .closed => 0x43
  | .maintenance => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SessionState :=
  if byte = 0x50 then .preOpen
  else if byte = 0x4F then .opened
  else if byte = 0x52 then .regulatoryHalt
  else if byte = 0x48 then .halted
  else if byte = 0x43 then .closed
  else .maintenance

def ofByte (byte : UInt8) : SessionState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SessionState) : ofByte value.toByte = value := by
  cases value with
  | preOpen => decide
  | opened => decide
  | regulatoryHalt => decide
  | halted => decide
  | closed => decide
  | maintenance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SessionState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SessionState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SessionState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SessionState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SessionState

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x53, 0x42]

inductive Side where
  | sell -- Sell
  | buy -- Buy
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .sell => 0x53
  | .buy => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x53 then .sell
  else .buy

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | sell => decide
  | buy => decide
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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x54, 0x74, 0x4C, 0x6C, 0x53, 0x73, 0x52, 0x72, 0x41, 0x61, 0x42, 0x62]

inductive TradeType where
  | normalTrade -- Normal Trade
  | normalCross -- Normal Cross
  | auctionTrade -- Auction Trade
  | auctionCross -- Auction Cross
  | combinationToUnderlyingTrade -- Combination To Underlying Trade
  | combinationToUnderlyingCross -- Combination To Underlying Cross
  | combinationToCombinationTrade -- Combination To Combination Trade
  | combinationToCombinationCross -- Combination To Combination Cross
  | stripToStripTrade -- Strip To Strip Trade
  | stripToStripCross -- Strip To Strip Cross
  | stripToOutrightTrade -- Strip To Outright Trade
  | stripToOutrightCross -- Strip To Outright Cross
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .normalTrade => 0x54
  | .normalCross => 0x74
  | .auctionTrade => 0x4C
  | .auctionCross => 0x6C
  | .combinationToUnderlyingTrade => 0x53
  | .combinationToUnderlyingCross => 0x73
  | .combinationToCombinationTrade => 0x52
  | .combinationToCombinationCross => 0x72
  | .stripToStripTrade => 0x41
  | .stripToStripCross => 0x61
  | .stripToOutrightTrade => 0x42
  | .stripToOutrightCross => 0x62
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x54 then .normalTrade
  else if byte = 0x74 then .normalCross
  else if byte = 0x4C then .auctionTrade
  else if byte = 0x6C then .auctionCross
  else if byte = 0x53 then .combinationToUnderlyingTrade
  else if byte = 0x73 then .combinationToUnderlyingCross
  else if byte = 0x52 then .combinationToCombinationTrade
  else if byte = 0x72 then .combinationToCombinationCross
  else if byte = 0x41 then .stripToStripTrade
  else if byte = 0x61 then .stripToStripCross
  else if byte = 0x42 then .stripToOutrightTrade
  else .stripToOutrightCross

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | normalTrade => decide
  | normalCross => decide
  | auctionTrade => decide
  | auctionCross => decide
  | combinationToUnderlyingTrade => decide
  | combinationToUnderlyingCross => decide
  | combinationToCombinationTrade => decide
  | combinationToCombinationCross => decide
  | stripToStripTrade => decide
  | stripToStripCross => decide
  | stripToOutrightTrade => decide
  | stripToOutrightCross => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Opposite Side: one byte code -/
def OppositeSide.codes : List UInt8 :=
  [0x53, 0x42]

inductive OppositeSide where
  | sell -- Sell
  | buy -- Buy
  | unlisted (byte : { byte : UInt8 // byte ∉ OppositeSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OppositeSide

def toByte : OppositeSide → UInt8
  | .sell => 0x53
  | .buy => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OppositeSide :=
  if byte = 0x53 then .sell
  else .buy

def ofByte (byte : UInt8) : OppositeSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OppositeSide) : ofByte value.toByte = value := by
  cases value with
  | sell => decide
  | buy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OppositeSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OppositeSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OppositeSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OppositeSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OppositeSide

/-- Buyer Side: one byte code -/
def BuyerSide.codes : List UInt8 :=
  [0x53, 0x42]

inductive BuyerSide where
  | sell -- Sell
  | buy -- Buy
  | unlisted (byte : { byte : UInt8 // byte ∉ BuyerSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuyerSide

def toByte : BuyerSide → UInt8
  | .sell => 0x53
  | .buy => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuyerSide :=
  if byte = 0x53 then .sell
  else .buy

def ofByte (byte : UInt8) : BuyerSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuyerSide) : ofByte value.toByte = value := by
  cases value with
  | sell => decide
  | buy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuyerSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuyerSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuyerSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuyerSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuyerSide

/-- Seller Side: one byte code -/
def SellerSide.codes : List UInt8 :=
  [0x53, 0x42]

inductive SellerSide where
  | sell -- Sell
  | buy -- Buy
  | unlisted (byte : { byte : UInt8 // byte ∉ SellerSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SellerSide

def toByte : SellerSide → UInt8
  | .sell => 0x53
  | .buy => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SellerSide :=
  if byte = 0x53 then .sell
  else .buy

def ofByte (byte : UInt8) : SellerSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SellerSide) : ofByte value.toByte = value := by
  cases value with
  | sell => decide
  | buy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SellerSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SellerSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SellerSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SellerSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SellerSide

/-- Rfq Side: one byte code -/
def RfqSide.codes : List UInt8 :=
  [0x54, 0x42, 0x53, 0x58]

inductive RfqSide where
  | twoSidedQuote -- Two Sided Quote
  | bidQuote -- Bid Quote
  | askQuote -- Ask Quote
  | crossing -- Crossing
  | unlisted (byte : { byte : UInt8 // byte ∉ RfqSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RfqSide

def toByte : RfqSide → UInt8
  | .twoSidedQuote => 0x54
  | .bidQuote => 0x42
  | .askQuote => 0x53
  | .crossing => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RfqSide :=
  if byte = 0x54 then .twoSidedQuote
  else if byte = 0x42 then .bidQuote
  else if byte = 0x53 then .askQuote
  else .crossing

def ofByte (byte : UInt8) : RfqSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RfqSide) : ofByte value.toByte = value := by
  cases value with
  | twoSidedQuote => decide
  | bidQuote => decide
  | askQuote => decide
  | crossing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RfqSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RfqSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RfqSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RfqSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RfqSide

/-- Seconds Message: 4 bytes -/
structure SecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsMessage

/-- End Of Business Trade Date Message: 7 bytes -/
structure EndOfBusinessTradeDateMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace EndOfBusinessTradeDateMessage

def encode (message : EndOfBusinessTradeDateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (EndOfBusinessTradeDateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, tradeDate, eventCode }, bytes)

@[simp] theorem encode_length (message : EndOfBusinessTradeDateMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : EndOfBusinessTradeDateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfBusinessTradeDateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end EndOfBusinessTradeDateMessage

/-- Future Symbol Directory Message: 179 bytes -/
structure FutureSymbolDirectoryMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  symbolName : Alpha 32
  longName : Alpha 60
  isin : Alpha 12
  exchange : Alpha 6
  instrument : Alpha 6
  cfiCode : Alpha 6
  expiryYear : BitVec 16
  expiryMonth : BitVec 8
  priceDisplayDecimals : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 32
  lastTradingDate : BitVec 32
  priorDaySettlement : BitVec 64
  currency : Alpha 3
  lotSizeOrFaceValue : BitVec 64
  maturityValue : BitVec 8
  couponRate : BitVec 16
  paymentsPerYear : BitVec 8
  blockLotSize : BitVec 32
  expiryDate : BitVec 32
  deriving DecidableEq, Repr

namespace FutureSymbolDirectoryMessage

def encode (message : FutureSymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Alpha.encode message.symbolName
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.exchange
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUInt 2 message.expiryYear
    ++ (encodeUInt 1 message.expiryMonth
    ++ (encodeUInt 1 message.priceDisplayDecimals
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 4 message.priceMinimumTick
    ++ (encodeUInt 4 message.lastTradingDate
    ++ (encodeUInt 8 message.priorDaySettlement
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 8 message.lotSizeOrFaceValue
    ++ (encodeUInt 1 message.maturityValue
    ++ (encodeUInt 2 message.couponRate
    ++ (encodeUInt 1 message.paymentsPerYear
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 4 message.expiryDate))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureSymbolDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (symbolName, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 60 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (exchange, bytes) ← Alpha.decode 6 bytes
  let (instrument, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (expiryYear, bytes) ← decodeUInt 2 bytes
  let (expiryMonth, bytes) ← decodeUInt 1 bytes
  let (priceDisplayDecimals, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 4 bytes
  let (lastTradingDate, bytes) ← decodeUInt 4 bytes
  let (priorDaySettlement, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (lotSizeOrFaceValue, bytes) ← decodeUInt 8 bytes
  let (maturityValue, bytes) ← decodeUInt 1 bytes
  let (couponRate, bytes) ← decodeUInt 2 bytes
  let (paymentsPerYear, bytes) ← decodeUInt 1 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, symbolName, longName, isin, exchange, instrument, cfiCode, expiryYear, expiryMonth, priceDisplayDecimals, priceFractionalDenominator, priceMinimumTick, lastTradingDate, priorDaySettlement, currency, lotSizeOrFaceValue, maturityValue, couponRate, paymentsPerYear, blockLotSize, expiryDate }, bytes)

@[simp] theorem encode_length (message : FutureSymbolDirectoryMessage) : (encode message).length = 179 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FutureSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureSymbolDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FutureSymbolDirectoryMessage

/-- Options Symbol Directory Message: 219 bytes -/
structure OptionsSymbolDirectoryMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  symbolName : Alpha 32
  longName : Alpha 60
  isin : Alpha 12
  exchange : Alpha 6
  instrument : Alpha 6
  cfiCode : Alpha 6
  expiryYear : BitVec 16
  expiryMonth : BitVec 8
  optionType : OptionType
  strike : BitVec 64
  underlyingTradeableInstrumentId : BitVec 32
  priceDisplayDecimals : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 32
  strikePriceDecimalPosition : BitVec 8
  strikePriceFractionalDenominator : BitVec 32
  strikePriceMinimumTick : BitVec 32
  lastTradingDate : BitVec 32
  priorDaySettlement : BitVec 64
  volatility : BitVec 64
  currency : Alpha 3
  lotSizeOrFaceValue : BitVec 64
  maturityValue : BitVec 8
  couponRate : BitVec 16
  paymentsPerYear : BitVec 8
  blockLotSize : BitVec 32
  expiryDate : BitVec 32
  basisOfQuotation : Alpha 10
  deriving DecidableEq, Repr

namespace OptionsSymbolDirectoryMessage

def encode (message : OptionsSymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Alpha.encode message.symbolName
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.exchange
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUInt 2 message.expiryYear
    ++ (encodeUInt 1 message.expiryMonth
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 8 message.strike
    ++ (encodeUInt 4 message.underlyingTradeableInstrumentId
    ++ (encodeUInt 1 message.priceDisplayDecimals
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 4 message.priceMinimumTick
    ++ (encodeUInt 1 message.strikePriceDecimalPosition
    ++ (encodeUInt 4 message.strikePriceFractionalDenominator
    ++ (encodeUInt 4 message.strikePriceMinimumTick
    ++ (encodeUInt 4 message.lastTradingDate
    ++ (encodeUInt 8 message.priorDaySettlement
    ++ (encodeUInt 8 message.volatility
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 8 message.lotSizeOrFaceValue
    ++ (encodeUInt 1 message.maturityValue
    ++ (encodeUInt 2 message.couponRate
    ++ (encodeUInt 1 message.paymentsPerYear
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 4 message.expiryDate
    ++ (Alpha.encode message.basisOfQuotation))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionsSymbolDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (symbolName, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 60 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (exchange, bytes) ← Alpha.decode 6 bytes
  let (instrument, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (expiryYear, bytes) ← decodeUInt 2 bytes
  let (expiryMonth, bytes) ← decodeUInt 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (strike, bytes) ← decodeUInt 8 bytes
  let (underlyingTradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (priceDisplayDecimals, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 4 bytes
  let (strikePriceDecimalPosition, bytes) ← decodeUInt 1 bytes
  let (strikePriceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (strikePriceMinimumTick, bytes) ← decodeUInt 4 bytes
  let (lastTradingDate, bytes) ← decodeUInt 4 bytes
  let (priorDaySettlement, bytes) ← decodeUInt 8 bytes
  let (volatility, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (lotSizeOrFaceValue, bytes) ← decodeUInt 8 bytes
  let (maturityValue, bytes) ← decodeUInt 1 bytes
  let (couponRate, bytes) ← decodeUInt 2 bytes
  let (paymentsPerYear, bytes) ← decodeUInt 1 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (basisOfQuotation, bytes) ← Alpha.decode 10 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, symbolName, longName, isin, exchange, instrument, cfiCode, expiryYear, expiryMonth, optionType, strike, underlyingTradeableInstrumentId, priceDisplayDecimals, priceFractionalDenominator, priceMinimumTick, strikePriceDecimalPosition, strikePriceFractionalDenominator, strikePriceMinimumTick, lastTradingDate, priorDaySettlement, volatility, currency, lotSizeOrFaceValue, maturityValue, couponRate, paymentsPerYear, blockLotSize, expiryDate, basisOfQuotation }, bytes)

@[simp] theorem encode_length (message : OptionsSymbolDirectoryMessage) : (encode message).length = 219 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length]

theorem encode_length_pos (message : OptionsSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionsSymbolDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionsSymbolDirectoryMessage

/-- Combination Leg: 17 bytes -/
structure CombinationLeg where
  tradeableInstrumentIdLeg : BitVec 32
  sideLeg : SideLeg
  ratioLeg : BitVec 32
  priceLeg : BitVec 64
  deriving DecidableEq, Repr

namespace CombinationLeg

def encode (message : CombinationLeg) : List UInt8 :=
  encodeUInt 4 message.tradeableInstrumentIdLeg
    ++ (SideLeg.encode message.sideLeg
    ++ (encodeUInt 4 message.ratioLeg
    ++ (encodeUInt 8 message.priceLeg)))

def decode (bytes : List UInt8) : Option (CombinationLeg × List UInt8) := do
  let (tradeableInstrumentIdLeg, bytes) ← decodeUInt 4 bytes
  let (sideLeg, bytes) ← SideLeg.decode bytes
  let (ratioLeg, bytes) ← decodeUInt 4 bytes
  let (priceLeg, bytes) ← decodeUInt 8 bytes
  pure ({ tradeableInstrumentIdLeg, sideLeg, ratioLeg, priceLeg }, bytes)

@[simp] theorem encode_length (message : CombinationLeg) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SideLeg.encode_length]

theorem encode_length_pos (message : CombinationLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SideLeg.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CombinationLeg

/-- Combination Symbol Directory Message: 221 bytes -/
structure CombinationSymbolDirectoryMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  symbolName : Alpha 32
  longName : Alpha 60
  cfiCode : Alpha 6
  priceMethod : BitVec 8
  priceDisplayDecimals : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 32
  legs : BitVec 8
  combinationLeg : Exact 6 CombinationLeg
  deriving DecidableEq, Repr

namespace CombinationSymbolDirectoryMessage

def encode (message : CombinationSymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Alpha.encode message.symbolName
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUInt 1 message.priceMethod
    ++ (encodeUInt 1 message.priceDisplayDecimals
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 4 message.priceMinimumTick
    ++ (encodeUInt 1 message.legs
    ++ (encodeMany CombinationLeg.encode message.combinationLeg.val)))))))))))

def decode (bytes : List UInt8) : Option (CombinationSymbolDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (symbolName, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 60 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (priceMethod, bytes) ← decodeUInt 1 bytes
  let (priceDisplayDecimals, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 4 bytes
  let (legs, bytes) ← decodeUInt 1 bytes
  let (combinationLeg_, bytes) ← decodeMany CombinationLeg.decode 6 bytes
  if fits_combinationLeg : combinationLeg_.length = 6 then
    pure ({ nanoseconds, tradeDate, tradeableInstrumentId, symbolName, longName, cfiCode, priceMethod, priceDisplayDecimals, priceFractionalDenominator, priceMinimumTick, legs, combinationLeg := ⟨combinationLeg_, fits_combinationLeg⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : CombinationSymbolDirectoryMessage) : (encode message).length = 221 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeMany_length_const CombinationLeg.encode 17 CombinationLeg.encode_length, message.combinationLeg.length_eq]

theorem encode_length_pos (message : CombinationSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationSymbolDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [decodeMany_exact 6 CombinationLeg.encode CombinationLeg.decode CombinationLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.combinationLeg.length_eq]
  rfl

end CombinationSymbolDirectoryMessage

/-- Bundle Leg: 17 bytes -/
structure BundleLeg where
  tradeableInstrumentIdLeg : BitVec 32
  sideLeg : SideLeg
  ratioLeg : BitVec 32
  priceLeg : BitVec 64
  deriving DecidableEq, Repr

namespace BundleLeg

def encode (message : BundleLeg) : List UInt8 :=
  encodeUInt 4 message.tradeableInstrumentIdLeg
    ++ (SideLeg.encode message.sideLeg
    ++ (encodeUInt 4 message.ratioLeg
    ++ (encodeUInt 8 message.priceLeg)))

def decode (bytes : List UInt8) : Option (BundleLeg × List UInt8) := do
  let (tradeableInstrumentIdLeg, bytes) ← decodeUInt 4 bytes
  let (sideLeg, bytes) ← SideLeg.decode bytes
  let (ratioLeg, bytes) ← decodeUInt 4 bytes
  let (priceLeg, bytes) ← decodeUInt 8 bytes
  pure ({ tradeableInstrumentIdLeg, sideLeg, ratioLeg, priceLeg }, bytes)

@[simp] theorem encode_length (message : BundleLeg) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SideLeg.encode_length]

theorem encode_length_pos (message : BundleLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BundleLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SideLeg.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BundleLeg

/-- Bundles Symbol Directory: 459 bytes -/
structure BundlesSymbolDirectory where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  symbolName : Alpha 32
  longName : Alpha 60
  cfiCode : Alpha 6
  priceMethod : BitVec 8
  priceDisplayDecimals : BitVec 8
  priceFractionalDenominator : BitVec 32
  priceMinimumTick : BitVec 32
  legs : BitVec 8
  bundleLeg : Exact 20 BundleLeg
  deriving DecidableEq, Repr

namespace BundlesSymbolDirectory

def encode (message : BundlesSymbolDirectory) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Alpha.encode message.symbolName
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUInt 1 message.priceMethod
    ++ (encodeUInt 1 message.priceDisplayDecimals
    ++ (encodeUInt 4 message.priceFractionalDenominator
    ++ (encodeUInt 4 message.priceMinimumTick
    ++ (encodeUInt 1 message.legs
    ++ (encodeMany BundleLeg.encode message.bundleLeg.val)))))))))))

def decode (bytes : List UInt8) : Option (BundlesSymbolDirectory × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (symbolName, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 60 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (priceMethod, bytes) ← decodeUInt 1 bytes
  let (priceDisplayDecimals, bytes) ← decodeUInt 1 bytes
  let (priceFractionalDenominator, bytes) ← decodeUInt 4 bytes
  let (priceMinimumTick, bytes) ← decodeUInt 4 bytes
  let (legs, bytes) ← decodeUInt 1 bytes
  let (bundleLeg_, bytes) ← decodeMany BundleLeg.decode 20 bytes
  if fits_bundleLeg : bundleLeg_.length = 20 then
    pure ({ nanoseconds, tradeDate, tradeableInstrumentId, symbolName, longName, cfiCode, priceMethod, priceDisplayDecimals, priceFractionalDenominator, priceMinimumTick, legs, bundleLeg := ⟨bundleLeg_, fits_bundleLeg⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : BundlesSymbolDirectory) : (encode message).length = 459 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeMany_length_const BundleLeg.encode 17 BundleLeg.encode_length, message.bundleLeg.length_eq]

theorem encode_length_pos (message : BundlesSymbolDirectory) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BundlesSymbolDirectory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [decodeMany_exact 20 BundleLeg.encode BundleLeg.decode BundleLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bundleLeg.length_eq]
  rfl

end BundlesSymbolDirectory

/-- Order Book State Message: 11 bytes -/
structure OrderBookStateMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  sessionState : SessionState
  deriving DecidableEq, Repr

namespace OrderBookStateMessage

def encode (message : OrderBookStateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (SessionState.encode message.sessionState)))

def decode (bytes : List UInt8) : Option (OrderBookStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (sessionState, bytes) ← SessionState.decode bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, sessionState }, bytes)

@[simp] theorem encode_length (message : OrderBookStateMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SessionState.encode_length]

theorem encode_length_pos (message : OrderBookStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SessionState.decode_encode, some_bind]
  rfl

end OrderBookStateMessage

/-- Add Order Message: 39 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  orderBookPriority : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price)))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Volume Cancelled Message: 23 bytes -/
structure OrderVolumeCancelledMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderVolumeCancelledMessage

def encode (message : OrderVolumeCancelledMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (OrderVolumeCancelledMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, quantity }, bytes)

@[simp] theorem encode_length (message : OrderVolumeCancelledMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderVolumeCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderVolumeCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderVolumeCancelledMessage

/-- Order Deleted Message: 19 bytes -/
structure OrderDeletedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeletedMessage

def encode (message : OrderDeletedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId))))

def decode (bytes : List UInt8) : Option (OrderDeletedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId }, bytes)

@[simp] theorem encode_length (message : OrderDeletedMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeletedMessage

/-- Order Executed Message: 55 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantityRemaining : BitVec 32
  tradeType : TradeType
  tradeId : BitVec 64
  executedQuantity : BitVec 32
  tradePrice : BitVec 64
  combinationTradeId : BitVec 64
  counterPartyId : Alpha 3
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.combinationTradeId
    ++ (Alpha.encode message.counterPartyId)))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (combinationTradeId, bytes) ← decodeUInt 8 bytes
  let (counterPartyId, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, quantityRemaining, tradeType, tradeId, executedQuantity, tradePrice, combinationTradeId, counterPartyId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Auction Order Executed Message: 52 bytes -/
structure AuctionOrderExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantityRemaining : BitVec 32
  tradeType : TradeType
  tradeId : BitVec 64
  executedQuantity : BitVec 32
  tradePrice : BitVec 64
  oppositeOrderId : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionOrderExecutedMessage

def encode (message : AuctionOrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.oppositeOrderId))))))))))

def decode (bytes : List UInt8) : Option (AuctionOrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (oppositeOrderId, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, quantityRemaining, tradeType, tradeId, executedQuantity, tradePrice, oppositeOrderId }, bytes)

@[simp] theorem encode_length (message : AuctionOrderExecutedMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : AuctionOrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionOrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AuctionOrderExecutedMessage

/-- Combination Order Executed Message: 65 bytes -/
structure CombinationOrderExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantityRemaining : BitVec 32
  tradeType : TradeType
  tradeId : BitVec 64
  executedQuantity : BitVec 32
  tradePrice : BitVec 64
  oppositeTradeableInstrumentId : BitVec 32
  oppositeSide : OppositeSide
  oppositeOrderId : BitVec 64
  combinationTradeId : BitVec 64
  deriving DecidableEq, Repr

namespace CombinationOrderExecutedMessage

def encode (message : CombinationOrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.quantityRemaining
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.oppositeTradeableInstrumentId
    ++ (OppositeSide.encode message.oppositeSide
    ++ (encodeUInt 8 message.oppositeOrderId
    ++ (encodeUInt 8 message.combinationTradeId)))))))))))))

def decode (bytes : List UInt8) : Option (CombinationOrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantityRemaining, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (oppositeTradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (oppositeSide, bytes) ← OppositeSide.decode bytes
  let (oppositeOrderId, bytes) ← decodeUInt 8 bytes
  let (combinationTradeId, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, quantityRemaining, tradeType, tradeId, executedQuantity, tradePrice, oppositeTradeableInstrumentId, oppositeSide, oppositeOrderId, combinationTradeId }, bytes)

@[simp] theorem encode_length (message : CombinationOrderExecutedMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeType.encode_length, OppositeSide.encode_length]

theorem encode_length_pos (message : CombinationOrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationOrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CombinationOrderExecutedMessage

/-- Implied Order Added Message: 39 bytes -/
structure ImpliedOrderAddedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  orderBookPriority : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace ImpliedOrderAddedMessage

def encode (message : ImpliedOrderAddedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price)))))))

def decode (bytes : List UInt8) : Option (ImpliedOrderAddedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderAddedMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ImpliedOrderAddedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderAddedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ImpliedOrderAddedMessage

/-- Implied Order Replaced Message: 39 bytes -/
structure ImpliedOrderReplacedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  orderBookPriority : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace ImpliedOrderReplacedMessage

def encode (message : ImpliedOrderReplacedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.orderBookPriority
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price)))))))

def decode (bytes : List UInt8) : Option (ImpliedOrderReplacedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookPriority, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId, orderBookPriority, quantity, price }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderReplacedMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ImpliedOrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ImpliedOrderReplacedMessage

/-- Implied Order Deleted Message: 19 bytes -/
structure ImpliedOrderDeletedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  side : Side
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace ImpliedOrderDeletedMessage

def encode (message : ImpliedOrderDeletedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId))))

def decode (bytes : List UInt8) : Option (ImpliedOrderDeletedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, side, orderId }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderDeletedMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ImpliedOrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ImpliedOrderDeletedMessage

/-- Trade Executed Message: 45 bytes -/
structure TradeExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  tradeType : TradeType
  tradeId : BitVec 64
  executedQuantity : BitVec 32
  tradePrice : BitVec 64
  combinationTradeId : BitVec 64
  participantIdBuyer : Alpha 3
  participantIdSeller : Alpha 3
  deriving DecidableEq, Repr

namespace TradeExecutedMessage

def encode (message : TradeExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.combinationTradeId
    ++ (Alpha.encode message.participantIdBuyer
    ++ (Alpha.encode message.participantIdSeller)))))))))

def decode (bytes : List UInt8) : Option (TradeExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (combinationTradeId, bytes) ← decodeUInt 8 bytes
  let (participantIdBuyer, bytes) ← Alpha.decode 3 bytes
  let (participantIdSeller, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, tradeType, tradeId, executedQuantity, tradePrice, combinationTradeId, participantIdBuyer, participantIdSeller }, bytes)

@[simp] theorem encode_length (message : TradeExecutedMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeExecutedMessage

/-- Combination Trade Executed Message: 79 bytes -/
structure CombinationTradeExecutedMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  tradeType : TradeType
  tradeId : BitVec 64
  executedQuantity : BitVec 32
  tradePrice : BitVec 64
  buyerTradeableInstrumentId : BitVec 32
  buyerSide : BuyerSide
  buyerOrderId : BitVec 64
  buyerCombinationTradeId : BitVec 64
  buyerParticipantId : Alpha 3
  sellerTradeableInstrumentId : BitVec 32
  sellerSide : SellerSide
  sellerOrderId : BitVec 64
  sellerCombinationTradeId : BitVec 64
  sellerParticipantId : Alpha 3
  deriving DecidableEq, Repr

namespace CombinationTradeExecutedMessage

def encode (message : CombinationTradeExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.buyerTradeableInstrumentId
    ++ (BuyerSide.encode message.buyerSide
    ++ (encodeUInt 8 message.buyerOrderId
    ++ (encodeUInt 8 message.buyerCombinationTradeId
    ++ (Alpha.encode message.buyerParticipantId
    ++ (encodeUInt 4 message.sellerTradeableInstrumentId
    ++ (SellerSide.encode message.sellerSide
    ++ (encodeUInt 8 message.sellerOrderId
    ++ (encodeUInt 8 message.sellerCombinationTradeId
    ++ (Alpha.encode message.sellerParticipantId))))))))))))))))

def decode (bytes : List UInt8) : Option (CombinationTradeExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (buyerTradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (buyerSide, bytes) ← BuyerSide.decode bytes
  let (buyerOrderId, bytes) ← decodeUInt 8 bytes
  let (buyerCombinationTradeId, bytes) ← decodeUInt 8 bytes
  let (buyerParticipantId, bytes) ← Alpha.decode 3 bytes
  let (sellerTradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (sellerSide, bytes) ← SellerSide.decode bytes
  let (sellerOrderId, bytes) ← decodeUInt 8 bytes
  let (sellerCombinationTradeId, bytes) ← decodeUInt 8 bytes
  let (sellerParticipantId, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, tradeType, tradeId, executedQuantity, tradePrice, buyerTradeableInstrumentId, buyerSide, buyerOrderId, buyerCombinationTradeId, buyerParticipantId, sellerTradeableInstrumentId, sellerSide, sellerOrderId, sellerCombinationTradeId, sellerParticipantId }, bytes)

@[simp] theorem encode_length (message : CombinationTradeExecutedMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeType.encode_length, BuyerSide.encode_length, Alpha.encode_length, SellerSide.encode_length]

theorem encode_length_pos (message : CombinationTradeExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationTradeExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuyerSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SellerSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CombinationTradeExecutedMessage

/-- Trade Cancellation Message: 18 bytes -/
structure TradeCancellationMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  tradeId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (encodeUInt 8 message.tradeId)))

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, tradeId }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancellationMessage

/-- Equilibrium Price Message: 42 bytes -/
structure EquilibriumPriceMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  equilibriumPrice : BitVec 64
  matchedQuantity : BitVec 64
  bidQuantity : BitVec 64
  askQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace EquilibriumPriceMessage

def encode (message : EquilibriumPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (encodeUInt 8 message.equilibriumPrice
    ++ (encodeUInt 8 message.matchedQuantity
    ++ (encodeUInt 8 message.bidQuantity
    ++ (encodeUInt 8 message.askQuantity))))))

def decode (bytes : List UInt8) : Option (EquilibriumPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (matchedQuantity, bytes) ← decodeUInt 8 bytes
  let (bidQuantity, bytes) ← decodeUInt 8 bytes
  let (askQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, equilibriumPrice, matchedQuantity, bidQuantity, askQuantity }, bytes)

@[simp] theorem encode_length (message : EquilibriumPriceMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EquilibriumPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquilibriumPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquilibriumPriceMessage

/-- Open High Low Last Trade Adjustment Message: 54 bytes -/
structure OpenHighLowLastTradeAdjustmentMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  openingTrade : BitVec 64
  highestTrade : BitVec 64
  lowestTrade : BitVec 64
  lastTrade : BitVec 64
  lastVolume : BitVec 32
  totalTradedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace OpenHighLowLastTradeAdjustmentMessage

def encode (message : OpenHighLowLastTradeAdjustmentMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (encodeUInt 8 message.openingTrade
    ++ (encodeUInt 8 message.highestTrade
    ++ (encodeUInt 8 message.lowestTrade
    ++ (encodeUInt 8 message.lastTrade
    ++ (encodeUInt 4 message.lastVolume
    ++ (encodeUInt 8 message.totalTradedVolume))))))))

def decode (bytes : List UInt8) : Option (OpenHighLowLastTradeAdjustmentMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (openingTrade, bytes) ← decodeUInt 8 bytes
  let (highestTrade, bytes) ← decodeUInt 8 bytes
  let (lowestTrade, bytes) ← decodeUInt 8 bytes
  let (lastTrade, bytes) ← decodeUInt 8 bytes
  let (lastVolume, bytes) ← decodeUInt 4 bytes
  let (totalTradedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, openingTrade, highestTrade, lowestTrade, lastTrade, lastVolume, totalTradedVolume }, bytes)

@[simp] theorem encode_length (message : OpenHighLowLastTradeAdjustmentMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OpenHighLowLastTradeAdjustmentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenHighLowLastTradeAdjustmentMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenHighLowLastTradeAdjustmentMessage

/-- Market Settlement Message: 54 bytes -/
structure MarketSettlementMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  openingTrade : BitVec 64
  highestTrade : BitVec 64
  lowestTrade : BitVec 64
  lastTrade : BitVec 64
  lastVolume : BitVec 32
  totalTradedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace MarketSettlementMessage

def encode (message : MarketSettlementMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (encodeUInt 8 message.openingTrade
    ++ (encodeUInt 8 message.highestTrade
    ++ (encodeUInt 8 message.lowestTrade
    ++ (encodeUInt 8 message.lastTrade
    ++ (encodeUInt 4 message.lastVolume
    ++ (encodeUInt 8 message.totalTradedVolume))))))))

def decode (bytes : List UInt8) : Option (MarketSettlementMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (openingTrade, bytes) ← decodeUInt 8 bytes
  let (highestTrade, bytes) ← decodeUInt 8 bytes
  let (lowestTrade, bytes) ← decodeUInt 8 bytes
  let (lastTrade, bytes) ← decodeUInt 8 bytes
  let (lastVolume, bytes) ← decodeUInt 4 bytes
  let (totalTradedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, openingTrade, highestTrade, lowestTrade, lastTrade, lastVolume, totalTradedVolume }, bytes)

@[simp] theorem encode_length (message : MarketSettlementMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MarketSettlementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSettlementMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketSettlementMessage

/-- Text Message: 112 bytes -/
structure TextMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  sourceId : Alpha 6
  text : Alpha 100
  deriving DecidableEq, Repr

namespace TextMessage

def encode (message : TextMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (Alpha.encode message.sourceId
    ++ (Alpha.encode message.text)))

def decode (bytes : List UInt8) : Option (TextMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (sourceId, bytes) ← Alpha.decode 6 bytes
  let (text, bytes) ← Alpha.decode 100 bytes
  pure ({ nanoseconds, tradeDate, sourceId, text }, bytes)

@[simp] theorem encode_length (message : TextMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TextMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TextMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TextMessage

/-- Request For Quote Message: 15 bytes -/
structure RequestForQuoteMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  rfqSide : RfqSide
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace RequestForQuoteMessage

def encode (message : RequestForQuoteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (RfqSide.encode message.rfqSide
    ++ (encodeUInt 4 message.quantity))))

def decode (bytes : List UInt8) : Option (RequestForQuoteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (rfqSide, bytes) ← RfqSide.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, rfqSide, quantity }, bytes)

@[simp] theorem encode_length (message : RequestForQuoteMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, RfqSide.encode_length]

theorem encode_length_pos (message : RequestForQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RfqSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RequestForQuoteMessage

/-- Anomalous Order Threshold Publish Message: 58 bytes -/
structure AnomalousOrderThresholdPublishMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  aotPrice : BitVec 64
  aotUpperPrice : BitVec 64
  aotLowerPrice : BitVec 64
  etrPrice : BitVec 64
  etrUpperPrice : BitVec 64
  etrLowerPrice : BitVec 64
  deriving DecidableEq, Repr

namespace AnomalousOrderThresholdPublishMessage

def encode (message : AnomalousOrderThresholdPublishMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (encodeUInt 8 message.aotPrice
    ++ (encodeUInt 8 message.aotUpperPrice
    ++ (encodeUInt 8 message.aotLowerPrice
    ++ (encodeUInt 8 message.etrPrice
    ++ (encodeUInt 8 message.etrUpperPrice
    ++ (encodeUInt 8 message.etrLowerPrice))))))))

def decode (bytes : List UInt8) : Option (AnomalousOrderThresholdPublishMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (aotPrice, bytes) ← decodeUInt 8 bytes
  let (aotUpperPrice, bytes) ← decodeUInt 8 bytes
  let (aotLowerPrice, bytes) ← decodeUInt 8 bytes
  let (etrPrice, bytes) ← decodeUInt 8 bytes
  let (etrUpperPrice, bytes) ← decodeUInt 8 bytes
  let (etrLowerPrice, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, aotPrice, aotUpperPrice, aotLowerPrice, etrPrice, etrUpperPrice, etrLowerPrice }, bytes)

@[simp] theorem encode_length (message : AnomalousOrderThresholdPublishMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AnomalousOrderThresholdPublishMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AnomalousOrderThresholdPublishMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AnomalousOrderThresholdPublishMessage

/-- Volume And Open Interest Message: 28 bytes -/
structure VolumeAndOpenInterestMessage where
  nanoseconds : BitVec 32
  tradeDate : BitVec 16
  tradeableInstrumentId : BitVec 32
  cumulativeVolume : BitVec 64
  openInterest : BitVec 64
  voiTradeDate : BitVec 16
  deriving DecidableEq, Repr

namespace VolumeAndOpenInterestMessage

def encode (message : VolumeAndOpenInterestMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 2 message.tradeDate
    ++ (encodeUInt 4 message.tradeableInstrumentId
    ++ (encodeUInt 8 message.cumulativeVolume
    ++ (encodeUInt 8 message.openInterest
    ++ (encodeUInt 2 message.voiTradeDate)))))

def decode (bytes : List UInt8) : Option (VolumeAndOpenInterestMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 2 bytes
  let (tradeableInstrumentId, bytes) ← decodeUInt 4 bytes
  let (cumulativeVolume, bytes) ← decodeUInt 8 bytes
  let (openInterest, bytes) ← decodeUInt 8 bytes
  let (voiTradeDate, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, tradeDate, tradeableInstrumentId, cumulativeVolume, openInterest, voiTradeDate }, bytes)

@[simp] theorem encode_length (message : VolumeAndOpenInterestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : VolumeAndOpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VolumeAndOpenInterestMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end VolumeAndOpenInterestMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- 'T' 0x54
  | endOfBusinessTradeDateMessage (message : EndOfBusinessTradeDateMessage) -- 'S' 0x53
  | futureSymbolDirectoryMessage (message : FutureSymbolDirectoryMessage) -- 'f' 0x66
  | optionsSymbolDirectoryMessage (message : OptionsSymbolDirectoryMessage) -- 'h' 0x68
  | combinationSymbolDirectoryMessage (message : CombinationSymbolDirectoryMessage) -- 'M' 0x4D
  | bundlesSymbolDirectory (message : BundlesSymbolDirectory) -- 'm' 0x6D
  | orderBookStateMessage (message : OrderBookStateMessage) -- 'O' 0x4F
  | addOrderMessage (message : AddOrderMessage) -- 'A' 0x41
  | orderVolumeCancelledMessage (message : OrderVolumeCancelledMessage) -- 'X' 0x58
  | orderDeletedMessage (message : OrderDeletedMessage) -- 'D' 0x44
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'E' 0x45
  | auctionOrderExecutedMessage (message : AuctionOrderExecutedMessage) -- 'C' 0x43
  | combinationOrderExecutedMessage (message : CombinationOrderExecutedMessage) -- 'e' 0x65
  | impliedOrderAddedMessage (message : ImpliedOrderAddedMessage) -- 'j' 0x6A
  | impliedOrderReplacedMessage (message : ImpliedOrderReplacedMessage) -- 'l' 0x6C
  | impliedOrderDeletedMessage (message : ImpliedOrderDeletedMessage) -- 'k' 0x6B
  | tradeExecutedMessage (message : TradeExecutedMessage) -- 'P' 0x50
  | combinationTradeExecutedMessage (message : CombinationTradeExecutedMessage) -- 'p' 0x70
  | tradeCancellationMessage (message : TradeCancellationMessage) -- 'B' 0x42
  | equilibriumPriceMessage (message : EquilibriumPriceMessage) -- 'Z' 0x5A
  | openHighLowLastTradeAdjustmentMessage (message : OpenHighLowLastTradeAdjustmentMessage) -- 't' 0x74
  | marketSettlementMessage (message : MarketSettlementMessage) -- 'Y' 0x59
  | textMessage (message : TextMessage) -- 'x' 0x78
  | requestForQuoteMessage (message : RequestForQuoteMessage) -- 'q' 0x71
  | anomalousOrderThresholdPublishMessage (message : AnomalousOrderThresholdPublishMessage) -- 'W' 0x57
  | volumeAndOpenInterestMessage (message : VolumeAndOpenInterestMessage) -- 'V' 0x56
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .endOfBusinessTradeDateMessage _ => 83
  | .futureSymbolDirectoryMessage _ => 102
  | .optionsSymbolDirectoryMessage _ => 104
  | .combinationSymbolDirectoryMessage _ => 77
  | .bundlesSymbolDirectory _ => 109
  | .orderBookStateMessage _ => 79
  | .addOrderMessage _ => 65
  | .orderVolumeCancelledMessage _ => 88
  | .orderDeletedMessage _ => 68
  | .orderExecutedMessage _ => 69
  | .auctionOrderExecutedMessage _ => 67
  | .combinationOrderExecutedMessage _ => 101
  | .impliedOrderAddedMessage _ => 106
  | .impliedOrderReplacedMessage _ => 108
  | .impliedOrderDeletedMessage _ => 107
  | .tradeExecutedMessage _ => 80
  | .combinationTradeExecutedMessage _ => 112
  | .tradeCancellationMessage _ => 66
  | .equilibriumPriceMessage _ => 90
  | .openHighLowLastTradeAdjustmentMessage _ => 116
  | .marketSettlementMessage _ => 89
  | .textMessage _ => 120
  | .requestForQuoteMessage _ => 113
  | .anomalousOrderThresholdPublishMessage _ => 87
  | .volumeAndOpenInterestMessage _ => 86

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .endOfBusinessTradeDateMessage message => EndOfBusinessTradeDateMessage.encode message
  | .futureSymbolDirectoryMessage message => FutureSymbolDirectoryMessage.encode message
  | .optionsSymbolDirectoryMessage message => OptionsSymbolDirectoryMessage.encode message
  | .combinationSymbolDirectoryMessage message => CombinationSymbolDirectoryMessage.encode message
  | .bundlesSymbolDirectory message => BundlesSymbolDirectory.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderVolumeCancelledMessage message => OrderVolumeCancelledMessage.encode message
  | .orderDeletedMessage message => OrderDeletedMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .auctionOrderExecutedMessage message => AuctionOrderExecutedMessage.encode message
  | .combinationOrderExecutedMessage message => CombinationOrderExecutedMessage.encode message
  | .impliedOrderAddedMessage message => ImpliedOrderAddedMessage.encode message
  | .impliedOrderReplacedMessage message => ImpliedOrderReplacedMessage.encode message
  | .impliedOrderDeletedMessage message => ImpliedOrderDeletedMessage.encode message
  | .tradeExecutedMessage message => TradeExecutedMessage.encode message
  | .combinationTradeExecutedMessage message => CombinationTradeExecutedMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .equilibriumPriceMessage message => EquilibriumPriceMessage.encode message
  | .openHighLowLastTradeAdjustmentMessage message => OpenHighLowLastTradeAdjustmentMessage.encode message
  | .marketSettlementMessage message => MarketSettlementMessage.encode message
  | .textMessage message => TextMessage.encode message
  | .requestForQuoteMessage message => RequestForQuoteMessage.encode message
  | .anomalousOrderThresholdPublishMessage message => AnomalousOrderThresholdPublishMessage.encode message
  | .volumeAndOpenInterestMessage message => VolumeAndOpenInterestMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 83 then (EndOfBusinessTradeDateMessage.decode bytes).map fun (message, rest) => (.endOfBusinessTradeDateMessage message, rest)
  else if tag = 102 then (FutureSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.futureSymbolDirectoryMessage message, rest)
  else if tag = 104 then (OptionsSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.optionsSymbolDirectoryMessage message, rest)
  else if tag = 77 then (CombinationSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.combinationSymbolDirectoryMessage message, rest)
  else if tag = 109 then (BundlesSymbolDirectory.decode bytes).map fun (message, rest) => (.bundlesSymbolDirectory message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 88 then (OrderVolumeCancelledMessage.decode bytes).map fun (message, rest) => (.orderVolumeCancelledMessage message, rest)
  else if tag = 68 then (OrderDeletedMessage.decode bytes).map fun (message, rest) => (.orderDeletedMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (AuctionOrderExecutedMessage.decode bytes).map fun (message, rest) => (.auctionOrderExecutedMessage message, rest)
  else if tag = 101 then (CombinationOrderExecutedMessage.decode bytes).map fun (message, rest) => (.combinationOrderExecutedMessage message, rest)
  else if tag = 106 then (ImpliedOrderAddedMessage.decode bytes).map fun (message, rest) => (.impliedOrderAddedMessage message, rest)
  else if tag = 108 then (ImpliedOrderReplacedMessage.decode bytes).map fun (message, rest) => (.impliedOrderReplacedMessage message, rest)
  else if tag = 107 then (ImpliedOrderDeletedMessage.decode bytes).map fun (message, rest) => (.impliedOrderDeletedMessage message, rest)
  else if tag = 80 then (TradeExecutedMessage.decode bytes).map fun (message, rest) => (.tradeExecutedMessage message, rest)
  else if tag = 112 then (CombinationTradeExecutedMessage.decode bytes).map fun (message, rest) => (.combinationTradeExecutedMessage message, rest)
  else if tag = 66 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 90 then (EquilibriumPriceMessage.decode bytes).map fun (message, rest) => (.equilibriumPriceMessage message, rest)
  else if tag = 116 then (OpenHighLowLastTradeAdjustmentMessage.decode bytes).map fun (message, rest) => (.openHighLowLastTradeAdjustmentMessage message, rest)
  else if tag = 89 then (MarketSettlementMessage.decode bytes).map fun (message, rest) => (.marketSettlementMessage message, rest)
  else if tag = 120 then (TextMessage.decode bytes).map fun (message, rest) => (.textMessage message, rest)
  else if tag = 113 then (RequestForQuoteMessage.decode bytes).map fun (message, rest) => (.requestForQuoteMessage message, rest)
  else if tag = 87 then (AnomalousOrderThresholdPublishMessage.decode bytes).map fun (message, rest) => (.anomalousOrderThresholdPublishMessage message, rest)
  else if tag = 86 then (VolumeAndOpenInterestMessage.decode bytes).map fun (message, rest) => (.volumeAndOpenInterestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | secondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | endOfBusinessTradeDateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfBusinessTradeDateMessage.encode_length]
    omega
  | futureSymbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, FutureSymbolDirectoryMessage.encode_length]
    omega
  | optionsSymbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionsSymbolDirectoryMessage.encode_length]
    omega
  | combinationSymbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationSymbolDirectoryMessage.encode_length]
    omega
  | bundlesSymbolDirectory inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BundlesSymbolDirectory.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderVolumeCancelledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderVolumeCancelledMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeletedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | auctionOrderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionOrderExecutedMessage.encode_length]
    omega
  | combinationOrderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationOrderExecutedMessage.encode_length]
    omega
  | impliedOrderAddedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImpliedOrderAddedMessage.encode_length]
    omega
  | impliedOrderReplacedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImpliedOrderReplacedMessage.encode_length]
    omega
  | impliedOrderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImpliedOrderDeletedMessage.encode_length]
    omega
  | tradeExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeExecutedMessage.encode_length]
    omega
  | combinationTradeExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationTradeExecutedMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCancellationMessage.encode_length]
    omega
  | equilibriumPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquilibriumPriceMessage.encode_length]
    omega
  | openHighLowLastTradeAdjustmentMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpenHighLowLastTradeAdjustmentMessage.encode_length]
    omega
  | marketSettlementMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketSettlementMessage.encode_length]
    omega
  | textMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TextMessage.encode_length]
    omega
  | requestForQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RequestForQuoteMessage.encode_length]
    omega
  | anomalousOrderThresholdPublishMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AnomalousOrderThresholdPublishMessage.encode_length]
    omega
  | volumeAndOpenInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, VolumeAndOpenInterestMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.AsxAsxderivativesNtpItchV105
