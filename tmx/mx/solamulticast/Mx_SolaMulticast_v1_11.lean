import Omi.Wire

/-!
# TMX Group Sola Multicast v1.11

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Number Of Level counts Option Market Depth Trading Instrument in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Level counts Future Options Market Depth Trading Instrument in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Level counts Futures Market Depth Trading Instrument in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Level counts Strategy Market Depth Trading Instrument in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Level counts Swap Future Market Depth Trading Instrument in ascii digits: it is written from the list as its digits, and a list of more than 9 could not be written.

Note: Number Of Legs counts Strategy Summary Strategy Leg in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Entries counts Tick Entry Group in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolamulticastHsvfV111

/-- Call Put Code: one byte code -/
def CallPutCode.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallPutCode where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutCode

def toByte : CallPutCode → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutCode :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallPutCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutCode) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CallPutCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutCode

/-- Requested Market Side: one byte code -/
def RequestedMarketSide.codes : List UInt8 :=
  [0x42, 0x53, 0x32]

inductive RequestedMarketSide where
  | buy -- Buy
  | sell -- Sell
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestedMarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestedMarketSide

def toByte : RequestedMarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .both => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestedMarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .both

def ofByte (byte : UInt8) : RequestedMarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestedMarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestedMarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestedMarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestedMarketSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RequestedMarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestedMarketSide

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x41, 0x45]

inductive OptionType where
  | american -- American
  | european -- European
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .american => 0x41
  | .european => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x41 then .american
  else .european

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
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

/-- Delivery Type: one byte code -/
def DeliveryType.codes : List UInt8 :=
  [0x43, 0x50]

inductive DeliveryType where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryType

def toByte : DeliveryType → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryType :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : DeliveryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeliveryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryType

/-- Strategy Allow Implied: one byte code -/
def StrategyAllowImplied.codes : List UInt8 :=
  [0x59, 0x4E]

inductive StrategyAllowImplied where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyAllowImplied.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyAllowImplied

def toByte : StrategyAllowImplied → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyAllowImplied :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : StrategyAllowImplied :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyAllowImplied) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyAllowImplied) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyAllowImplied × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyAllowImplied) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyAllowImplied) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyAllowImplied

/-- Day Count Convention: one byte code -/
def DayCountConvention.codes : List UInt8 :=
  [0x41, 0x42, 0x43]

inductive DayCountConvention where
  | act365 -- Act 365
  | act360 -- Act 360
  | thirty360 -- Thirty 360
  | unlisted (byte : { byte : UInt8 // byte ∉ DayCountConvention.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DayCountConvention

def toByte : DayCountConvention → UInt8
  | .act365 => 0x41
  | .act360 => 0x42
  | .thirty360 => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DayCountConvention :=
  if byte = 0x41 then .act365
  else if byte = 0x42 then .act360
  else .thirty360

def ofByte (byte : UInt8) : DayCountConvention :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DayCountConvention) : ofByte value.toByte = value := by
  cases value with
  | act365 => decide
  | act360 => decide
  | thirty360 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DayCountConvention) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DayCountConvention × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DayCountConvention) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DayCountConvention) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DayCountConvention

/-- Tick: one byte code -/
def Tick.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive Tick where
  | uptick -- Uptick
  | downtick -- Downtick
  | unlisted (byte : { byte : UInt8 // byte ∉ Tick.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tick

def toByte : Tick → UInt8
  | .uptick => 0x2B
  | .downtick => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tick :=
  if byte = 0x2B then .uptick
  else .downtick

def ofByte (byte : UInt8) : Tick :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tick) : ofByte value.toByte = value := by
  cases value with
  | uptick => decide
  | downtick => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tick) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tick × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tick) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tick) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tick

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x53, 0x45, 0x55, 0x43]

inductive Reason where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | instrumentNewOrUpdate -- Instrument New Or Update
  | tradeCancellation -- Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .instrumentNewOrUpdate => 0x55
  | .tradeCancellation => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x53 then .startOfDay
  else if byte = 0x45 then .endOfDay
  else if byte = 0x55 then .instrumentNewOrUpdate
  else .tradeCancellation

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | instrumentNewOrUpdate => decide
  | tradeCancellation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Leg Ratio Sign: one byte code -/
def LegRatioSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LegRatioSign where
  | buyOfTheUnderlying -- Buy Of The Underlying
  | sellOfTheUnderlying -- Sell Of The Underlying
  | unlisted (byte : { byte : UInt8 // byte ∉ LegRatioSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegRatioSign

def toByte : LegRatioSign → UInt8
  | .buyOfTheUnderlying => 0x2B
  | .sellOfTheUnderlying => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegRatioSign :=
  if byte = 0x2B then .buyOfTheUnderlying
  else .sellOfTheUnderlying

def ofByte (byte : UInt8) : LegRatioSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegRatioSign) : ofByte value.toByte = value := by
  cases value with
  | buyOfTheUnderlying => decide
  | sellOfTheUnderlying => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegRatioSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegRatioSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegRatioSign) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegRatioSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegRatioSign

/-- Option Trade Message: 76 bytes -/
structure OptionTradeMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  secondFiller1 : Alpha 1
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, openInterest, secondFiller1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
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

/-- Future Options Trade Message: 77 bytes -/
structure FutureOptionsTradeMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  priceIndicatorMarker : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeMessage

def encode (message : FutureOptionsTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber)))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, volume, tradePrice, tradePriceFractionIndicator, priceIndicatorMarker, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, openInterest, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
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

end FutureOptionsTradeMessage

/-- Futures Trade Message: 59 bytes -/
structure FuturesTradeMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeMessage

def encode (message : FuturesTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FuturesTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeMessage

/-- Strategy Trade Message: 79 bytes -/
structure StrategyTradeMessage where
  exchangeId : Alpha 1
  symbolStrategy : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeMessage

def encode (message : StrategyTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, symbolStrategy, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Swap Future Trade Message: 61 bytes -/
structure SwapFutureTradeMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  tradeVolume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace SwapFutureTradeMessage

def encode (message : SwapFutureTradeMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.tradeVolume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureTradeMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeVolume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, tradeVolume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : SwapFutureTradeMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SwapFutureTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureTradeMessage

/-- Option Rfq Message: 30 bytes -/
structure OptionRfqMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace OptionRfqMessage

def encode (message : OptionRfqMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))))))))

def decode (bytes : List UInt8) : Option (OptionRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : OptionRfqMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : OptionRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end OptionRfqMessage

/-- Future Options Rfq Message: 30 bytes -/
structure FutureOptionsRfqMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureOptionsRfqMessage

def encode (message : FutureOptionsRfqMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureOptionsRfqMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureOptionsRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureOptionsRfqMessage

/-- Futures Rfq Message: 21 bytes -/
structure FuturesRfqMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FuturesRfqMessage

def encode (message : FuturesRfqMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))))

def decode (bytes : List UInt8) : Option (FuturesRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FuturesRfqMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FuturesRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesRfqMessage) (rest : List UInt8) :
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
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FuturesRfqMessage

/-- Strategy Rfq Message: 40 bytes -/
structure StrategyRfqMessage where
  exchangeId : Alpha 1
  symbolStrategy : Alpha 30
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace StrategyRfqMessage

def encode (message : StrategyRfqMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))

def decode (bytes : List UInt8) : Option (StrategyRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, symbolStrategy, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : StrategyRfqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : StrategyRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end StrategyRfqMessage

/-- Swap Future Rfq Message: 29 bytes -/
structure SwapFutureRfqMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace SwapFutureRfqMessage

def encode (message : SwapFutureRfqMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide)))))))))

def decode (bytes : List UInt8) : Option (SwapFutureRfqMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : SwapFutureRfqMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : SwapFutureRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end SwapFutureRfqMessage

/-- Instrument Schedule Notice Option Message: 28 bytes -/
structure InstrumentScheduleNoticeOptionMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceScheduleNotice : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeOptionMessage

def encode (message : InstrumentScheduleNoticeOptionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceScheduleNotice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceScheduleNotice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceScheduleNotice, strikePriceFractionIndicator, expiryYear, expiryDay, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeOptionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeOptionMessage

/-- Instrument Schedule Notice Futures Option Message: 28 bytes -/
structure InstrumentScheduleNoticeFuturesOptionMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFuturesOptionMessage

def encode (message : InstrumentScheduleNoticeFuturesOptionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFuturesOptionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFuturesOptionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFuturesOptionMessage

/-- Instrument Schedule Notice Future Message: 19 bytes -/
structure InstrumentScheduleNoticeFutureMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFutureMessage

def encode (message : InstrumentScheduleNoticeFutureMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFutureMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFutureMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFutureMessage

/-- Instrument Schedule Notice Strategy Message: 38 bytes -/
structure InstrumentScheduleNoticeStrategyMessage where
  exchangeId : Alpha 1
  strategySymbol : Alpha 30
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeStrategyMessage

def encode (message : InstrumentScheduleNoticeStrategyMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeStrategyMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, strategySymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeStrategyMessage) (rest : List UInt8) :
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

end InstrumentScheduleNoticeStrategyMessage

/-- Instrument Schedule Notice Swap Future Message: 27 bytes -/
structure InstrumentScheduleNoticeSwapFutureMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  seriesStatus : Alpha 1
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeSwapFutureMessage

def encode (message : InstrumentScheduleNoticeSwapFutureMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime)))))))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeSwapFutureMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (seriesStatus, bytes) ← Alpha.decode 1 bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeSwapFutureMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeSwapFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeSwapFutureMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeSwapFutureMessage

/-- Option Quote Message: 47 bytes -/
structure OptionQuoteMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  secondFiller1 : Alpha 1
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.instrumentStatusMarker)))))))))))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, secondFiller1, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Future Options Quote Message: 47 bytes -/
structure FutureOptionsQuoteMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionsQuoteMessage

def encode (message : FutureOptionsQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (Alpha.encode message.filler1)))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker, filler1 }, bytes)

@[simp] theorem encode_length (message : FutureOptionsQuoteMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : FutureOptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsQuoteMessage

/-- Futures Quote Message: 37 bytes -/
structure FuturesQuoteMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace FuturesQuoteMessage

def encode (message : FuturesQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker)))))))))))

def decode (bytes : List UInt8) : Option (FuturesQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FuturesQuoteMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesQuoteMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesQuoteMessage

/-- Strategy Quote Message: 58 bytes -/
structure StrategyQuoteMessage where
  exchangeId : Alpha 1
  symbolStrategy : Alpha 30
  bidPriceSign : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSign : Alpha 1
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace StrategyQuoteMessage

def encode (message : StrategyQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker))))))))))

def decode (bytes : List UInt8) : Option (StrategyQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, symbolStrategy, bidPriceSign, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceSign, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : StrategyQuoteMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyQuoteMessage) (rest : List UInt8) :
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

end StrategyQuoteMessage

/-- Swap Future Quote Message: 45 bytes -/
structure SwapFutureQuoteMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  instrumentStatusMarker : Alpha 1
  deriving DecidableEq, Repr

namespace SwapFutureQuoteMessage

def encode (message : SwapFutureQuoteMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.instrumentStatusMarker))))))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureQuoteMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, bidPriceQuote, bidPriceFractionIndicator, bidSize, askPriceQuote, askPriceFractionIndicator, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : SwapFutureQuoteMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SwapFutureQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureQuoteMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureQuoteMessage

/-- Option Market Depth Trading Instrument: 29 bytes -/
structure OptionMarketDepthTradingInstrument where
  levelOfMarketDepth : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace OptionMarketDepthTradingInstrument

def encode (message : OptionMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : OptionMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OptionMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionMarketDepthTradingInstrument) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionMarketDepthTradingInstrument

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  instrumentStatusMarker : Alpha 1
  optionMarketDepthTradingInstrument : Digited 1 OptionMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.optionMarketDepthTradingInstrument.val.length
    ++ (encodeMany OptionMarketDepthTradingInstrument.encode message.optionMarketDepthTradingInstrument.val))))))))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (optionMarketDepthTradingInstrument_, bytes) ← decodeMany OptionMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_optionMarketDepthTradingInstrument : optionMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, instrumentStatusMarker, optionMarketDepthTradingInstrument := ⟨optionMarketDepthTradingInstrument_, fits_optionMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 284 := by
  have bound_optionMarketDepthTradingInstrument := message.optionMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const OptionMarketDepthTradingInstrument.encode 29 OptionMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.optionMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany OptionMarketDepthTradingInstrument.encode OptionMarketDepthTradingInstrument.decode OptionMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.optionMarketDepthTradingInstrument.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Future Options Market Depth Trading Instrument: 29 bytes -/
structure FutureOptionsMarketDepthTradingInstrument where
  levelOfMarketDepth : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthTradingInstrument

def encode (message : FutureOptionsMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FutureOptionsMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FutureOptionsMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthTradingInstrument) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsMarketDepthTradingInstrument

/-- Future Options Market Depth Message -/
structure FutureOptionsMarketDepthMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  instrumentStatusMarker : Alpha 1
  futureOptionsMarketDepthTradingInstrument : Digited 1 FutureOptionsMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthMessage

def encode (message : FutureOptionsMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futureOptionsMarketDepthTradingInstrument.val.length
    ++ (encodeMany FutureOptionsMarketDepthTradingInstrument.encode message.futureOptionsMarketDepthTradingInstrument.val))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (futureOptionsMarketDepthTradingInstrument_, bytes) ← decodeMany FutureOptionsMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_futureOptionsMarketDepthTradingInstrument : futureOptionsMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, instrumentStatusMarker, futureOptionsMarketDepthTradingInstrument := ⟨futureOptionsMarketDepthTradingInstrument_, fits_futureOptionsMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureOptionsMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureOptionsMarketDepthMessage) : (encode message).length ≤ 284 := by
  have bound_futureOptionsMarketDepthTradingInstrument := message.futureOptionsMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, CallPutCode.encode_length, encodeDigits_length, encodeMany_length_const FutureOptionsMarketDepthTradingInstrument.encode 29 FutureOptionsMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futureOptionsMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FutureOptionsMarketDepthTradingInstrument.encode FutureOptionsMarketDepthTradingInstrument.decode FutureOptionsMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futureOptionsMarketDepthTradingInstrument.length_lt]
  rfl

end FutureOptionsMarketDepthMessage

/-- Futures Market Depth Trading Instrument: 29 bytes -/
structure FuturesMarketDepthTradingInstrument where
  levelOfMarketDepth : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FuturesMarketDepthTradingInstrument

def encode (message : FuturesMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FuturesMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FuturesMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesMarketDepthTradingInstrument) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesMarketDepthTradingInstrument

/-- Futures Market Depth Message -/
structure FuturesMarketDepthMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  instrumentStatusMarker : Alpha 1
  futuresMarketDepthTradingInstrument : Digited 1 FuturesMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace FuturesMarketDepthMessage

def encode (message : FuturesMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futuresMarketDepthTradingInstrument.val.length
    ++ (encodeMany FuturesMarketDepthTradingInstrument.encode message.futuresMarketDepthTradingInstrument.val)))))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (futuresMarketDepthTradingInstrument_, bytes) ← decodeMany FuturesMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_futuresMarketDepthTradingInstrument : futuresMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, instrumentStatusMarker, futuresMarketDepthTradingInstrument := ⟨futuresMarketDepthTradingInstrument_, fits_futuresMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : FuturesMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FuturesMarketDepthMessage) : (encode message).length ≤ 275 := by
  have bound_futuresMarketDepthTradingInstrument := message.futuresMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const FuturesMarketDepthTradingInstrument.encode 29 FuturesMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : FuturesMarketDepthMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futuresMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FuturesMarketDepthTradingInstrument.encode FuturesMarketDepthTradingInstrument.decode FuturesMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futuresMarketDepthTradingInstrument.length_lt]
  rfl

end FuturesMarketDepthMessage

/-- Strategy Market Depth Trading Instrument: 31 bytes -/
structure StrategyMarketDepthTradingInstrument where
  levelOfMarketDepth : Alpha 1
  bidPriceSign : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : Alpha 1
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace StrategyMarketDepthTradingInstrument

def encode (message : StrategyMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.levelOfMarketDepth
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthTradingInstrument × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceSign, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : StrategyMarketDepthTradingInstrument) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyMarketDepthTradingInstrument) (rest : List UInt8) :
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

end StrategyMarketDepthTradingInstrument

/-- Strategy Market Depth Message -/
structure StrategyMarketDepthMessage where
  exchangeId : Alpha 1
  symbolStrategy : Alpha 30
  instrumentStatusMarker : Alpha 1
  strategyMarketDepthTradingInstrument : Digited 1 StrategyMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace StrategyMarketDepthMessage

def encode (message : StrategyMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.strategyMarketDepthTradingInstrument.val.length
    ++ (encodeMany StrategyMarketDepthTradingInstrument.encode message.strategyMarketDepthTradingInstrument.val))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (strategyMarketDepthTradingInstrument_, bytes) ← decodeMany StrategyMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_strategyMarketDepthTradingInstrument : strategyMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, symbolStrategy, instrumentStatusMarker, strategyMarketDepthTradingInstrument := ⟨strategyMarketDepthTradingInstrument_, fits_strategyMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyMarketDepthMessage) : (encode message).length ≤ 312 := by
  have bound_strategyMarketDepthTradingInstrument := message.strategyMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const StrategyMarketDepthTradingInstrument.encode 31 StrategyMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyMarketDepthTradingInstrument.encode StrategyMarketDepthTradingInstrument.decode StrategyMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyMarketDepthTradingInstrument.length_lt]
  rfl

end StrategyMarketDepthMessage

/-- Swap Future Market Depth Trading Instrument: 29 bytes -/
structure SwapFutureMarketDepthTradingInstrument where
  level : Alpha 1
  bidPriceQuote : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace SwapFutureMarketDepthTradingInstrument

def encode (message : SwapFutureMarketDepthTradingInstrument) : List UInt8 :=
  Alpha.encode message.level
    ++ (Alpha.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (Alpha.encode message.askPriceQuote
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (SwapFutureMarketDepthTradingInstrument × List UInt8) := do
  let (level, bytes) ← Alpha.decode 1 bytes
  let (bidPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ level, bidPriceQuote, bidPriceFractionIndicator, bidSize, numberOfBidOrders, askPriceQuote, askPriceFractionIndicator, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : SwapFutureMarketDepthTradingInstrument) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SwapFutureMarketDepthTradingInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureMarketDepthTradingInstrument) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureMarketDepthTradingInstrument

/-- Swap Future Market Depth Message -/
structure SwapFutureMarketDepthMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  instrumentStatusMarker : Alpha 1
  swapFutureMarketDepthTradingInstrument : Digited 1 SwapFutureMarketDepthTradingInstrument
  deriving DecidableEq, Repr

namespace SwapFutureMarketDepthMessage

def encode (message : SwapFutureMarketDepthMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.swapFutureMarketDepthTradingInstrument.val.length
    ++ (encodeMany SwapFutureMarketDepthTradingInstrument.encode message.swapFutureMarketDepthTradingInstrument.val))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureMarketDepthMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← Alpha.decode 1 bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (swapFutureMarketDepthTradingInstrument_, bytes) ← decodeMany SwapFutureMarketDepthTradingInstrument.decode numberOfLevel bytes
  if fits_swapFutureMarketDepthTradingInstrument : swapFutureMarketDepthTradingInstrument_.length < 10 ^ 1 then
    pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, instrumentStatusMarker, swapFutureMarketDepthTradingInstrument := ⟨swapFutureMarketDepthTradingInstrument_, fits_swapFutureMarketDepthTradingInstrument⟩ }, bytes)
  else none

theorem encode_length_pos (message : SwapFutureMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SwapFutureMarketDepthMessage) : (encode message).length ≤ 283 := by
  have bound_swapFutureMarketDepthTradingInstrument := message.swapFutureMarketDepthTradingInstrument.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const SwapFutureMarketDepthTradingInstrument.encode 29 SwapFutureMarketDepthTradingInstrument.encode_length]
  omega

@[simp] theorem decode_encode (message : SwapFutureMarketDepthMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.swapFutureMarketDepthTradingInstrument.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany SwapFutureMarketDepthTradingInstrument.encode SwapFutureMarketDepthTradingInstrument.decode SwapFutureMarketDepthTradingInstrument.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.swapFutureMarketDepthTradingInstrument.length_lt]
  rfl

end SwapFutureMarketDepthMessage

/-- Option Trade Cancellation Message: 68 bytes -/
structure OptionTradeCancellationMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  secondFiller1 : Alpha 1
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, volume, tradePrice, tradePriceFractionIndicator, filler6, timestamp, openInterest, secondFiller1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Future Options Trade Cancellation Message: 69 bytes -/
structure FutureOptionsTradeCancellationMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  volume : Alpha 8
  price : Alpha 6
  priceFractionIndicator : Alpha 1
  priceIndicatorMarker : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCancellationMessage

def encode (message : FutureOptionsTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.priceFractionIndicator
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 6 bytes
  let (priceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, volume, price, priceFractionIndicator, priceIndicatorMarker, filler6, timestamp, openInterest, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCancellationMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCancellationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCancellationMessage

/-- Futures Trade Cancellation Message: 51 bytes -/
structure FuturesTradeCancellationMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCancellationMessage

def encode (message : FuturesTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, volume, tradePrice, tradePriceFractionIndicator, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCancellationMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FuturesTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCancellationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCancellationMessage

/-- Strategy Trade Cancellation Message: 71 bytes -/
structure StrategyTradeCancellationMessage where
  exchangeId : Alpha 1
  symbolStrategy : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  filler1 : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeCancellationMessage

def encode (message : StrategyTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.tradeNumber)))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, symbolStrategy, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, filler6, timestamp, filler1, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCancellationMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCancellationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCancellationMessage

/-- Swap Future Trade Cancellation Message: 53 bytes -/
structure SwapFutureTradeCancellationMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  timestamp : Alpha 9
  marketPriceIndicator : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace SwapFutureTradeCancellationMessage

def encode (message : SwapFutureTradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.marketPriceIndicator
    ++ (Alpha.encode message.tradeNumber)))))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureTradeCancellationMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (marketPriceIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, volume, tradePrice, tradePriceFractionIndicator, timestamp, marketPriceIndicator, tradeNumber }, bytes)

@[simp] theorem encode_length (message : SwapFutureTradeCancellationMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SwapFutureTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureTradeCancellationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureTradeCancellationMessage

/-- Option Instrument Keys Message: 127 bytes -/
structure OptionInstrumentKeysMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptions : Alpha 6
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceOptions : Alpha 6
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  optionType : OptionType
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : Alpha 2
  underlyingSymbolRootOptions : Alpha 10
  contractSize : Alpha 8
  tickValue : Alpha 6
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPriceOptions
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceOptions
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRootOptions
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRootOptions, bytes) ← Alpha.decode 10 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 6 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptions, maximumThresholdPriceFractionIndicator, minimumThresholdPriceOptions, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRootOptions, contractSize, tickValue, tickValueFractionIndicator, currency, deliveryType }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 127 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, OptionType.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Future Options Instrument Keys Message: 114 bytes -/
structure FutureOptionsInstrumentKeysMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptions : Alpha 6
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceOptions : Alpha 6
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 6
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace FutureOptionsInstrumentKeysMessage

def encode (message : FutureOptionsInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPriceOptions
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceOptions
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 6 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptions, maximumThresholdPriceFractionIndicator, minimumThresholdPriceOptions, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValue, tickValueFractionIndicator, currency, deliveryType }, bytes)

@[simp] theorem encode_length (message : FutureOptionsInstrumentKeysMessage) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : FutureOptionsInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsInstrumentKeysMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end FutureOptionsInstrumentKeysMessage

/-- Underlying Instrument Keys Message: 37 bytes -/
structure UnderlyingInstrumentKeysMessage where
  exchangeId : Alpha 1
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  deriving DecidableEq, Repr

namespace UnderlyingInstrumentKeysMessage

def encode (message : UnderlyingInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode)))

def decode (bytes : List UInt8) : Option (UnderlyingInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  pure ({ exchangeId, groupInstrument, instrument, instrumentExternalCode }, bytes)

@[simp] theorem encode_length (message : UnderlyingInstrumentKeysMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingInstrumentKeysMessage) (rest : List UInt8) :
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

end UnderlyingInstrumentKeysMessage

/-- Futures Instrument Keys Message: 123 bytes -/
structure FuturesInstrumentKeysMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFutures : Alpha 6
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceFutures : Alpha 6
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 6
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  underlyingSymbol : Alpha 10
  deliveryType : DeliveryType
  associatedProductRootSymbol : Alpha 6
  associatedProductDeliveryMonth : Alpha 1
  associatedProductDeliveryYear : Alpha 2
  associatedProductExpiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace FuturesInstrumentKeysMessage

def encode (message : FuturesInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPriceFutures
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceFutures
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.underlyingSymbol
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.associatedProductRootSymbol
    ++ (Alpha.encode message.associatedProductDeliveryMonth
    ++ (Alpha.encode message.associatedProductDeliveryYear
    ++ (Alpha.encode message.associatedProductExpiryDay))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FuturesInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFutures, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceFutures, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 6 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 10 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (associatedProductRootSymbol, bytes) ← Alpha.decode 6 bytes
  let (associatedProductDeliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (associatedProductDeliveryYear, bytes) ← Alpha.decode 2 bytes
  let (associatedProductExpiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFutures, maximumThresholdPriceFractionIndicator, minimumThresholdPriceFutures, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValue, tickValueFractionIndicator, currency, underlyingSymbol, deliveryType, associatedProductRootSymbol, associatedProductDeliveryMonth, associatedProductDeliveryYear, associatedProductExpiryDay }, bytes)

@[simp] theorem encode_length (message : FuturesInstrumentKeysMessage) : (encode message).length = 123 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : FuturesInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FuturesInstrumentKeysMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesInstrumentKeysMessage

/-- Strategy Instrument Keys Message: 108 bytes -/
structure StrategyInstrumentKeysMessage where
  exchangeId : Alpha 1
  strategySymbol : Alpha 30
  expiryYear : Alpha 2
  deliveryMonth : Alpha 1
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptions : Alpha 6
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceOptions : Alpha 6
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  strategyAllowImplied : StrategyAllowImplied
  deriving DecidableEq, Repr

namespace StrategyInstrumentKeysMessage

def encode (message : StrategyInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPriceOptions
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceOptions
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (StrategyAllowImplied.encode message.strategyAllowImplied)))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (strategyAllowImplied, bytes) ← StrategyAllowImplied.decode bytes
  pure ({ exchangeId, strategySymbol, expiryYear, deliveryMonth, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptions, maximumThresholdPriceFractionIndicator, minimumThresholdPriceOptions, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, strategyAllowImplied }, bytes)

@[simp] theorem encode_length (message : StrategyInstrumentKeysMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, StrategyAllowImplied.encode_length]

theorem encode_length_pos (message : StrategyInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInstrumentKeysMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StrategyAllowImplied.decode_encode, some_bind]
  rfl

end StrategyInstrumentKeysMessage

/-- Swap Future Instrument Keys Message: 172 bytes -/
structure SwapFutureInstrumentKeysMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceOptions : Alpha 6
  maximumThresholdPriceFractionIndicator : Alpha 1
  minimumThresholdPriceOptions : Alpha 6
  minimumThresholdPriceFractionIndicator : Alpha 1
  tickIncrement : Alpha 6
  tickIncrementFractionIndicator : Alpha 1
  marketFlow : Alpha 2
  groupInstrument : Alpha 2
  instrumentId : Alpha 4
  externalSymbol : Alpha 30
  contractSize : Alpha 8
  tickValue : Alpha 6
  tickValueFractionIndicator : Alpha 1
  currency : Alpha 3
  effectiveDate : Alpha 6
  initialEffectiveDate : Alpha 6
  cashFlowAlignmentDate : Alpha 6
  paymentFrequency : Alpha 2
  resetFrequency : Alpha 2
  notionalPrincipalAmount : Alpha 8
  notionalPrincipalAmountFactionIndicator : Alpha 1
  dayCountConvention : DayCountConvention
  firstPaymentDate : Alpha 6
  nextPaymentDate : Alpha 6
  firstResetDate : Alpha 6
  nextResetDate : Alpha 6
  previousResetDate : Alpha 6
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace SwapFutureInstrumentKeysMessage

def encode (message : SwapFutureInstrumentKeysMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (Alpha.encode message.maximumThresholdPriceOptions
    ++ (Alpha.encode message.maximumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.minimumThresholdPriceOptions
    ++ (Alpha.encode message.minimumThresholdPriceFractionIndicator
    ++ (Alpha.encode message.tickIncrement
    ++ (Alpha.encode message.tickIncrementFractionIndicator
    ++ (Alpha.encode message.marketFlow
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.externalSymbol
    ++ (Alpha.encode message.contractSize
    ++ (Alpha.encode message.tickValue
    ++ (Alpha.encode message.tickValueFractionIndicator
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.effectiveDate
    ++ (Alpha.encode message.initialEffectiveDate
    ++ (Alpha.encode message.cashFlowAlignmentDate
    ++ (Alpha.encode message.paymentFrequency
    ++ (Alpha.encode message.resetFrequency
    ++ (Alpha.encode message.notionalPrincipalAmount
    ++ (Alpha.encode message.notionalPrincipalAmountFactionIndicator
    ++ (DayCountConvention.encode message.dayCountConvention
    ++ (Alpha.encode message.firstPaymentDate
    ++ (Alpha.encode message.nextPaymentDate
    ++ (Alpha.encode message.firstResetDate
    ++ (Alpha.encode message.nextResetDate
    ++ (Alpha.encode message.previousResetDate
    ++ (DeliveryType.encode message.deliveryType)))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SwapFutureInstrumentKeysMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (minimumThresholdPriceOptions, bytes) ← Alpha.decode 6 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickIncrement, bytes) ← Alpha.decode 6 bytes
  let (tickIncrementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (marketFlow, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrumentId, bytes) ← Alpha.decode 4 bytes
  let (externalSymbol, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValue, bytes) ← Alpha.decode 6 bytes
  let (tickValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (effectiveDate, bytes) ← Alpha.decode 6 bytes
  let (initialEffectiveDate, bytes) ← Alpha.decode 6 bytes
  let (cashFlowAlignmentDate, bytes) ← Alpha.decode 6 bytes
  let (paymentFrequency, bytes) ← Alpha.decode 2 bytes
  let (resetFrequency, bytes) ← Alpha.decode 2 bytes
  let (notionalPrincipalAmount, bytes) ← Alpha.decode 8 bytes
  let (notionalPrincipalAmountFactionIndicator, bytes) ← Alpha.decode 1 bytes
  let (dayCountConvention, bytes) ← DayCountConvention.decode bytes
  let (firstPaymentDate, bytes) ← Alpha.decode 6 bytes
  let (nextPaymentDate, bytes) ← Alpha.decode 6 bytes
  let (firstResetDate, bytes) ← Alpha.decode 6 bytes
  let (nextResetDate, bytes) ← Alpha.decode 6 bytes
  let (previousResetDate, bytes) ← Alpha.decode 6 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceOptions, maximumThresholdPriceFractionIndicator, minimumThresholdPriceOptions, minimumThresholdPriceFractionIndicator, tickIncrement, tickIncrementFractionIndicator, marketFlow, groupInstrument, instrumentId, externalSymbol, contractSize, tickValue, tickValueFractionIndicator, currency, effectiveDate, initialEffectiveDate, cashFlowAlignmentDate, paymentFrequency, resetFrequency, notionalPrincipalAmount, notionalPrincipalAmountFactionIndicator, dayCountConvention, firstPaymentDate, nextPaymentDate, firstResetDate, nextResetDate, previousResetDate, deliveryType }, bytes)

@[simp] theorem encode_length (message : SwapFutureInstrumentKeysMessage) : (encode message).length = 172 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, DayCountConvention.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : SwapFutureInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SwapFutureInstrumentKeysMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, DayCountConvention.decode_encode, some_bind]
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
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end SwapFutureInstrumentKeysMessage

/-- Option Summary Message: 124 bytes -/
structure OptionSummaryMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  bidPriceSummary : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openInterest : Alpha 7
  tick : Tick
  volume : Alpha 8
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  openPrice : Alpha 6
  openPriceFractionIndicator : Alpha 1
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  optionMarker : Alpha 2
  underlyingSymbolRootOptions : Alpha 10
  settlementPrice : Alpha 6
  settlementPriceFractionIndicatorOptions : Alpha 1
  previousSettlementPrice : Alpha 6
  previousSettlementPriceFractionIndicator : Alpha 1
  reason : Reason
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRootOptions
    ++ (Alpha.encode message.settlementPrice
    ++ (Alpha.encode message.settlementPriceFractionIndicatorOptions
    ++ (Alpha.encode message.previousSettlementPrice
    ++ (Alpha.encode message.previousSettlementPriceFractionIndicator
    ++ (Reason.encode message.reason))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRootOptions, bytes) ← Alpha.decode 10 bytes
  let (settlementPrice, bytes) ← Alpha.decode 6 bytes
  let (settlementPriceFractionIndicatorOptions, bytes) ← Alpha.decode 1 bytes
  let (previousSettlementPrice, bytes) ← Alpha.decode 6 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, optionMarker, underlyingSymbolRootOptions, settlementPrice, settlementPriceFractionIndicatorOptions, previousSettlementPrice, previousSettlementPriceFractionIndicator, reason }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 124 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Tick.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
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
  rw [Reason.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Future Options Summary Message: 119 bytes -/
structure FutureOptionsSummaryMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  bidPriceSummary : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openInterest : Alpha 7
  tick : Tick
  volume : Alpha 8
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  openingPrice : Alpha 6
  openingPriceFractionIndicator : Alpha 1
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  filler2 : Alpha 2
  underlyingSymbolRootFutureOptions : Alpha 3
  deliveryMonth : Alpha 1
  deliveryYearUnderlying : Alpha 1
  settlementPrice : Alpha 6
  settlementPriceFractionIndicatorFutures : Alpha 1
  previousSettlementPrice : Alpha 6
  previousSettlementPriceFractionIndicator : Alpha 1
  reason : Reason
  deriving DecidableEq, Repr

namespace FutureOptionsSummaryMessage

def encode (message : FutureOptionsSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.openingPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.underlyingSymbolRootFutureOptions
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearUnderlying
    ++ (Alpha.encode message.settlementPrice
    ++ (Alpha.encode message.settlementPriceFractionIndicatorFutures
    ++ (Alpha.encode message.previousSettlementPrice
    ++ (Alpha.encode message.previousSettlementPriceFractionIndicator
    ++ (Reason.encode message.reason))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openingPrice, bytes) ← Alpha.decode 6 bytes
  let (openingPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRootFutureOptions, bytes) ← Alpha.decode 3 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearUnderlying, bytes) ← Alpha.decode 1 bytes
  let (settlementPrice, bytes) ← Alpha.decode 6 bytes
  let (settlementPriceFractionIndicatorFutures, bytes) ← Alpha.decode 1 bytes
  let (previousSettlementPrice, bytes) ← Alpha.decode 6 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openInterest, tick, volume, netChangeSign, netChange, netChangeFractionIndicator, openingPrice, openingPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, filler2, underlyingSymbolRootFutureOptions, deliveryMonth, deliveryYearUnderlying, settlementPrice, settlementPriceFractionIndicatorFutures, previousSettlementPrice, previousSettlementPriceFractionIndicator, reason }, bytes)

@[simp] theorem encode_length (message : FutureOptionsSummaryMessage) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length, Tick.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FutureOptionsSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
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
  rw [Reason.decode_encode, some_bind]
  rfl

end FutureOptionsSummaryMessage

/-- Futures Summary Message: 109 bytes -/
structure FuturesSummaryMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  bidPriceSummary : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openPrice : Alpha 6
  openPriceFractionIndicator : Alpha 1
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  settlementPrice : Alpha 6
  settlementPriceFractionIndicatorFutures : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  volume : Alpha 8
  previousSettlement : Alpha 6
  previousSettlementFractionIndicator : Alpha 1
  openInterest : Alpha 7
  reason : Reason
  externalPriceAtSource : Alpha 6
  externalPriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace FuturesSummaryMessage

def encode (message : FuturesSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.settlementPrice
    ++ (Alpha.encode message.settlementPriceFractionIndicatorFutures
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.previousSettlement
    ++ (Alpha.encode message.previousSettlementFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Reason.encode message.reason
    ++ (Alpha.encode message.externalPriceAtSource
    ++ (Alpha.encode message.externalPriceFractionIndicator))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (settlementPrice, bytes) ← Alpha.decode 6 bytes
  let (settlementPriceFractionIndicatorFutures, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlement, bytes) ← Alpha.decode 6 bytes
  let (previousSettlementFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (externalPriceAtSource, bytes) ← Alpha.decode 6 bytes
  let (externalPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, settlementPrice, settlementPriceFractionIndicatorFutures, netChangeSign, netChange, netChangeFractionIndicator, volume, previousSettlement, previousSettlementFractionIndicator, openInterest, reason, externalPriceAtSource, externalPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : FuturesSummaryMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FuturesSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesSummaryMessage

/-- Strategy Summary Strategy Leg: 33 bytes -/
structure StrategySummaryStrategyLeg where
  legRatioSign : LegRatioSign
  legRatio : Alpha 2
  legSymbol : Alpha 30
  deriving DecidableEq, Repr

namespace StrategySummaryStrategyLeg

def encode (message : StrategySummaryStrategyLeg) : List UInt8 :=
  LegRatioSign.encode message.legRatioSign
    ++ (Alpha.encode message.legRatio
    ++ (Alpha.encode message.legSymbol))

def decode (bytes : List UInt8) : Option (StrategySummaryStrategyLeg × List UInt8) := do
  let (legRatioSign, bytes) ← LegRatioSign.decode bytes
  let (legRatio, bytes) ← Alpha.decode 2 bytes
  let (legSymbol, bytes) ← Alpha.decode 30 bytes
  pure ({ legRatioSign, legRatio, legSymbol }, bytes)

@[simp] theorem encode_length (message : StrategySummaryStrategyLeg) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, LegRatioSign.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategySummaryStrategyLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategySummaryStrategyLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegRatioSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategySummaryStrategyLeg

/-- Strategy Summary Message -/
structure StrategySummaryMessage where
  exchangeId : Alpha 1
  strategySymbol : Alpha 30
  bidPriceSign : Alpha 1
  bidPriceSummary : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSign : Alpha 1
  askPriceSummary : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPriceSign : Alpha 1
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openPriceSign : Alpha 1
  openPrice : Alpha 6
  openPriceFractionIndicator : Alpha 1
  highPriceSign : Alpha 1
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPriceSign : Alpha 1
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  volume : Alpha 8
  reason : Reason
  strategySummaryStrategyLeg : Digited 2 StrategySummaryStrategyLeg
  deriving DecidableEq, Repr

namespace StrategySummaryMessage

def encode (message : StrategySummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.bidPriceSign
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSign
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPriceSign
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPriceSign
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPriceSign
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPriceSign
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Reason.encode message.reason
    ++ (encodeDigits 2 message.strategySummaryStrategyLeg.val.length
    ++ (encodeMany StrategySummaryStrategyLeg.encode message.strategySummaryStrategyLeg.val))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (StrategySummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← Alpha.decode 1 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPriceSign, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPriceSign, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPriceSign, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (strategySummaryStrategyLeg_, bytes) ← decodeMany StrategySummaryStrategyLeg.decode numberOfLegs bytes
  if fits_strategySummaryStrategyLeg : strategySummaryStrategyLeg_.length < 10 ^ 2 then
    pure ({ exchangeId, strategySymbol, bidPriceSign, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSign, askPriceSummary, askPriceFractionIndicator, askSize, lastPriceSign, lastPrice, lastPriceFractionIndicator, openPriceSign, openPrice, openPriceFractionIndicator, highPriceSign, highPrice, highPriceFractionIndicator, lowPriceSign, lowPrice, lowPriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume, reason, strategySummaryStrategyLeg := ⟨strategySummaryStrategyLeg_, fits_strategySummaryStrategyLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategySummaryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategySummaryMessage) : (encode message).length ≤ 3375 := by
  have bound_strategySummaryStrategyLeg := message.strategySummaryStrategyLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, Reason.encode_length, encodeDigits_length, encodeMany_length_const StrategySummaryStrategyLeg.encode 33 StrategySummaryStrategyLeg.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : StrategySummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategySummaryStrategyLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategySummaryStrategyLeg.encode StrategySummaryStrategyLeg.decode StrategySummaryStrategyLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategySummaryStrategyLeg.length_lt]
  rfl

end StrategySummaryMessage

/-- Swap Future Summary Message: 153 bytes -/
structure SwapFutureSummaryMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  bidPriceSummary : Alpha 6
  bidPriceFractionIndicator : Alpha 1
  bidSize : Alpha 5
  askPriceSummary : Alpha 6
  askPriceFractionIndicator : Alpha 1
  askSize : Alpha 5
  lastPrice : Alpha 6
  lastPriceFractionIndicator : Alpha 1
  openPrice : Alpha 6
  openPriceFractionIndicator : Alpha 1
  highPrice : Alpha 6
  highPriceFractionIndicator : Alpha 1
  lowPrice : Alpha 6
  lowPriceFractionIndicator : Alpha 1
  settlementPrice : Alpha 6
  settlementPriceFractionIndicatorFutures : Alpha 1
  netPresentValueA : Alpha 11
  netPresentValueFractionIndicator : Alpha 1
  historicalCouponB : Alpha 11
  historicalCouponFractionIndicator : Alpha 1
  priceAlignmentInterestC : Alpha 11
  priceAlignmentInterestFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  volume : Alpha 8
  previousSettlementPrice : Alpha 6
  previousSettlementPriceFractionIndicator : Alpha 1
  previousResetRate : Alpha 6
  previousResetRateFractionIndicator : Alpha 1
  openInterest : Alpha 7
  reason : Reason
  deriving DecidableEq, Repr

namespace SwapFutureSummaryMessage

def encode (message : SwapFutureSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.bidPriceSummary
    ++ (Alpha.encode message.bidPriceFractionIndicator
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPriceSummary
    ++ (Alpha.encode message.askPriceFractionIndicator
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.lastPrice
    ++ (Alpha.encode message.lastPriceFractionIndicator
    ++ (Alpha.encode message.openPrice
    ++ (Alpha.encode message.openPriceFractionIndicator
    ++ (Alpha.encode message.highPrice
    ++ (Alpha.encode message.highPriceFractionIndicator
    ++ (Alpha.encode message.lowPrice
    ++ (Alpha.encode message.lowPriceFractionIndicator
    ++ (Alpha.encode message.settlementPrice
    ++ (Alpha.encode message.settlementPriceFractionIndicatorFutures
    ++ (Alpha.encode message.netPresentValueA
    ++ (Alpha.encode message.netPresentValueFractionIndicator
    ++ (Alpha.encode message.historicalCouponB
    ++ (Alpha.encode message.historicalCouponFractionIndicator
    ++ (Alpha.encode message.priceAlignmentInterestC
    ++ (Alpha.encode message.priceAlignmentInterestFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.previousSettlementPrice
    ++ (Alpha.encode message.previousSettlementPriceFractionIndicator
    ++ (Alpha.encode message.previousResetRate
    ++ (Alpha.encode message.previousResetRateFractionIndicator
    ++ (Alpha.encode message.openInterest
    ++ (Reason.encode message.reason)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SwapFutureSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (bidPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummary, bytes) ← Alpha.decode 6 bytes
  let (askPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPrice, bytes) ← Alpha.decode 6 bytes
  let (lastPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openPrice, bytes) ← Alpha.decode 6 bytes
  let (openPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (highPrice, bytes) ← Alpha.decode 6 bytes
  let (highPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (lowPrice, bytes) ← Alpha.decode 6 bytes
  let (lowPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (settlementPrice, bytes) ← Alpha.decode 6 bytes
  let (settlementPriceFractionIndicatorFutures, bytes) ← Alpha.decode 1 bytes
  let (netPresentValueA, bytes) ← Alpha.decode 11 bytes
  let (netPresentValueFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (historicalCouponB, bytes) ← Alpha.decode 11 bytes
  let (historicalCouponFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceAlignmentInterestC, bytes) ← Alpha.decode 11 bytes
  let (priceAlignmentInterestFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlementPrice, bytes) ← Alpha.decode 6 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (previousResetRate, bytes) ← Alpha.decode 6 bytes
  let (previousResetRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, bidPriceSummary, bidPriceFractionIndicator, bidSize, askPriceSummary, askPriceFractionIndicator, askSize, lastPrice, lastPriceFractionIndicator, openPrice, openPriceFractionIndicator, highPrice, highPriceFractionIndicator, lowPrice, lowPriceFractionIndicator, settlementPrice, settlementPriceFractionIndicatorFutures, netPresentValueA, netPresentValueFractionIndicator, historicalCouponB, historicalCouponFractionIndicator, priceAlignmentInterestC, priceAlignmentInterestFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, volume, previousSettlementPrice, previousSettlementPriceFractionIndicator, previousResetRate, previousResetRateFractionIndicator, openInterest, reason }, bytes)

@[simp] theorem encode_length (message : SwapFutureSummaryMessage) : (encode message).length = 153 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Reason.encode_length]

theorem encode_length_pos (message : SwapFutureSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SwapFutureSummaryMessage) (rest : List UInt8) :
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
  rw [Reason.decode_encode, some_bind]
  rfl

end SwapFutureSummaryMessage

/-- Beginning Of Options Summary Message: 1 bytes -/
structure BeginningOfOptionsSummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfOptionsSummaryMessage

def encode (message : BeginningOfOptionsSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfOptionsSummaryMessage

/-- Beginning Of Future Options Summary Message: 1 bytes -/
structure BeginningOfFutureOptionsSummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfFutureOptionsSummaryMessage

def encode (message : BeginningOfFutureOptionsSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfFutureOptionsSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfFutureOptionsSummaryMessage

/-- Beginning Of Futures Summary Message: 1 bytes -/
structure BeginningOfFuturesSummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfFuturesSummaryMessage

def encode (message : BeginningOfFuturesSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfFuturesSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFuturesSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfFuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfFuturesSummaryMessage

/-- Beginning Of Strategy Summary Message: 1 bytes -/
structure BeginningOfStrategySummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace BeginningOfStrategySummaryMessage

def encode (message : BeginningOfStrategySummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (BeginningOfStrategySummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfStrategySummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BeginningOfStrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfStrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BeginningOfStrategySummaryMessage

/-- Swap Future Beginning Of Summary Message: 1 bytes -/
structure SwapFutureBeginningOfSummaryMessage where
  exchangeId : Alpha 1
  deriving DecidableEq, Repr

namespace SwapFutureBeginningOfSummaryMessage

def encode (message : SwapFutureBeginningOfSummaryMessage) : List UInt8 :=
  Alpha.encode message.exchangeId

def decode (bytes : List UInt8) : Option (SwapFutureBeginningOfSummaryMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId }, bytes)

@[simp] theorem encode_length (message : SwapFutureBeginningOfSummaryMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SwapFutureBeginningOfSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureBeginningOfSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureBeginningOfSummaryMessage

/-- Option Trade Correction Message: 76 bytes -/
structure OptionTradeCorrectionMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  filler1 : Alpha 1
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  secondFiller1 : Alpha 1
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeCorrectionMessage

def encode (message : OptionTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, filler1, strikePriceInstrument, strikePriceFractionIndicator, expiryYear, expiryDay, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, openInterest, secondFiller1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeCorrectionMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OptionTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCorrectionMessage) (rest : List UInt8) :
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

end OptionTradeCorrectionMessage

/-- Future Options Trade Correction Message: 77 bytes -/
structure FutureOptionsTradeCorrectionMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  contractMonthCode : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceInstrument : Alpha 7
  strikePriceFractionIndicator : Alpha 1
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  priceIndicatorMarker : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  openInterest : Alpha 7
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCorrectionMessage

def encode (message : FutureOptionsTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.contractMonthCode
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.strikePriceInstrument
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber)))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (contractMonthCode, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceInstrument, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, contractMonthCode, expiryYear, expiryDay, callPutCode, strikePriceInstrument, strikePriceFractionIndicator, volume, tradePrice, tradePriceFractionIndicator, priceIndicatorMarker, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, openInterest, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCorrectionMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
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

end FutureOptionsTradeCorrectionMessage

/-- Futures Trade Correction Message: 59 bytes -/
structure FuturesTradeCorrectionMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  deliveryMonth : Alpha 1
  deliveryYearFutures : Alpha 2
  deliveryDay : Alpha 2
  volume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCorrectionMessage

def encode (message : FuturesTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.deliveryMonth
    ++ (Alpha.encode message.deliveryYearFutures
    ++ (Alpha.encode message.deliveryDay
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (deliveryMonth, bytes) ← Alpha.decode 1 bytes
  let (deliveryYearFutures, bytes) ← Alpha.decode 2 bytes
  let (deliveryDay, bytes) ← Alpha.decode 2 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, deliveryMonth, deliveryYearFutures, deliveryDay, volume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCorrectionMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FuturesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCorrectionMessage

/-- Strategy Trade Correction Message: 79 bytes -/
structure StrategyTradeCorrectionMessage where
  exchangeId : Alpha 1
  symbolStrategy : Alpha 30
  volume : Alpha 8
  tradePriceSign : Alpha 1
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  filler6 : Alpha 6
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeCorrectionMessage

def encode (message : StrategyTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.symbolStrategy
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePriceSign
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (symbolStrategy, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← Alpha.decode 1 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, symbolStrategy, volume, tradePriceSign, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, filler6, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCorrectionMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategyTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCorrectionMessage

/-- Swap Future Trade Correction Message: 61 bytes -/
structure SwapFutureTradeCorrectionMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  expiryMonth : Alpha 1
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  tenor : Alpha 2
  fixedRate : Alpha 5
  fixedRateFractionIndicator : Alpha 1
  tradeVolume : Alpha 8
  tradePrice : Alpha 6
  tradePriceFractionIndicator : Alpha 1
  netChangeSign : Alpha 1
  netChange : Alpha 6
  netChangeFractionIndicator : Alpha 1
  timestamp : Alpha 9
  priceIndicatorMarker : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace SwapFutureTradeCorrectionMessage

def encode (message : SwapFutureTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.expiryMonth
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.tenor
    ++ (Alpha.encode message.fixedRate
    ++ (Alpha.encode message.fixedRateFractionIndicator
    ++ (Alpha.encode message.tradeVolume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradePriceFractionIndicator
    ++ (Alpha.encode message.netChangeSign
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.netChangeFractionIndicator
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))))))))

def decode (bytes : List UInt8) : Option (SwapFutureTradeCorrectionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← Alpha.decode 1 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (tenor, bytes) ← Alpha.decode 2 bytes
  let (fixedRate, bytes) ← Alpha.decode 5 bytes
  let (fixedRateFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeVolume, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 6 bytes
  let (tradePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (netChangeSign, bytes) ← Alpha.decode 1 bytes
  let (netChange, bytes) ← Alpha.decode 6 bytes
  let (netChangeFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (timestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ exchangeId, rootSymbol, expiryMonth, expiryYear, expiryDay, tenor, fixedRate, fixedRateFractionIndicator, tradeVolume, tradePrice, tradePriceFractionIndicator, netChangeSign, netChange, netChangeFractionIndicator, timestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : SwapFutureTradeCorrectionMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SwapFutureTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SwapFutureTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SwapFutureTradeCorrectionMessage

/-- Group Status Message: 8 bytes -/
structure GroupStatusMessage where
  exchangeId : Alpha 1
  rootSymbol : Alpha 6
  groupStatus : Alpha 1
  deriving DecidableEq, Repr

namespace GroupStatusMessage

def encode (message : GroupStatusMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbol
    ++ (Alpha.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (GroupStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, rootSymbol, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : GroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupStatusMessage

/-- Strategies Message: 4 bytes -/
structure StrategiesMessage where
  exchangeId : Alpha 1
  groupInstrument : Alpha 2
  groupStatus : Alpha 1
  deriving DecidableEq, Repr

namespace StrategiesMessage

def encode (message : StrategiesMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.groupStatus))

def decode (bytes : List UInt8) : Option (StrategiesMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (groupStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ exchangeId, groupInstrument, groupStatus }, bytes)

@[simp] theorem encode_length (message : StrategiesMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StrategiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategiesMessage

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
  symbolBulletin : Alpha 30
  specialBulletinContents : Alpha 49
  continueMarker : Alpha 1
  deriving DecidableEq, Repr

namespace SpecialTextBulletin

def encode (message : SpecialTextBulletin) : List UInt8 :=
  Alpha.encode message.symbolBulletin
    ++ (Alpha.encode message.specialBulletinContents
    ++ (Alpha.encode message.continueMarker))

def decode (bytes : List UInt8) : Option (SpecialTextBulletin × List UInt8) := do
  let (symbolBulletin, bytes) ← Alpha.decode 30 bytes
  let (specialBulletinContents, bytes) ← Alpha.decode 49 bytes
  let (continueMarker, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolBulletin, specialBulletinContents, continueMarker }, bytes)

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
  reserved : Alpha 1
  bulletin : Bulletin
  deriving DecidableEq, Repr

namespace BulletinsMessage

def encode (message : BulletinsMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (encodeUInt 1 (Bulletin.tag message.bulletin)
    ++ (Bulletin.encode message.bulletin))

def decode (bytes : List UInt8) : Option (BulletinsMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (bulletinType, bytes) ← decodeUInt 1 bytes
  let (bulletin, bytes) ← Bulletin.decode bulletinType bytes
  pure ({ reserved, bulletin }, bytes)

theorem encode_length_pos (message : BulletinsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulletinsMessage) : (encode message).length ≤ 82 := by
  unfold encode
  cases message.bulletin with
  | regularTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpecialTextBulletin.encode_length]
    omega

@[simp] theorem decode_encode (message : BulletinsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Bulletin.decode_encode, some_bind]
  rfl

end BulletinsMessage

/-- End Of Sales Message: 7 bytes -/
structure EndOfSalesMessage where
  reserved : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfSalesMessage

def encode (message : EndOfSalesMessage) : List UInt8 :=
  Alpha.encode message.reserved
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfSalesMessage × List UInt8) := do
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved, time }, bytes)

@[simp] theorem encode_length (message : EndOfSalesMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfSalesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSalesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSalesMessage

/-- Tick Entry Group: 14 bytes -/
structure TickEntryGroup where
  minPrice : Alpha 6
  minPriceFractionIndicator : Alpha 1
  tickPrice : Alpha 6
  tickPriceFractionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace TickEntryGroup

def encode (message : TickEntryGroup) : List UInt8 :=
  Alpha.encode message.minPrice
    ++ (Alpha.encode message.minPriceFractionIndicator
    ++ (Alpha.encode message.tickPrice
    ++ (Alpha.encode message.tickPriceFractionIndicator)))

def decode (bytes : List UInt8) : Option (TickEntryGroup × List UInt8) := do
  let (minPrice, bytes) ← Alpha.decode 6 bytes
  let (minPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tickPrice, bytes) ← Alpha.decode 6 bytes
  let (tickPriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ minPrice, minPriceFractionIndicator, tickPrice, tickPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickEntryGroup) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TickEntryGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickEntryGroup) (rest : List UInt8) :
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

end TickEntryGroup

/-- Tick Table Message -/
structure TickTableMessage where
  exchangeId : Alpha 1
  tickTableName : Alpha 50
  tickTableShortName : Alpha 2
  tickEntryGroup : Digited 2 TickEntryGroup
  deriving DecidableEq, Repr

namespace TickTableMessage

def encode (message : TickTableMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.tickTableName
    ++ (Alpha.encode message.tickTableShortName
    ++ (encodeDigits 2 message.tickEntryGroup.val.length
    ++ (encodeMany TickEntryGroup.encode message.tickEntryGroup.val))))

def decode (bytes : List UInt8) : Option (TickTableMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (tickTableName, bytes) ← Alpha.decode 50 bytes
  let (tickTableShortName, bytes) ← Alpha.decode 2 bytes
  let (numberOfEntries, bytes) ← decodeDigits 2 bytes
  let (tickEntryGroup_, bytes) ← decodeMany TickEntryGroup.decode numberOfEntries bytes
  if fits_tickEntryGroup : tickEntryGroup_.length < 10 ^ 2 then
    pure ({ exchangeId, tickTableName, tickTableShortName, tickEntryGroup := ⟨tickEntryGroup_, fits_tickEntryGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TickTableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickTableMessage) : (encode message).length ≤ 1441 := by
  have bound_tickEntryGroup := message.tickEntryGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const TickEntryGroup.encode 14 TickEntryGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TickTableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.tickEntryGroup.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany TickEntryGroup.encode TickEntryGroup.decode TickEntryGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tickEntryGroup.length_lt]
  rfl

end TickTableMessage

/-- End Of Transmission Message: 7 bytes -/
structure EndOfTransmissionMessage where
  exchangeId : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmissionMessage

def encode (message : EndOfTransmissionMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (EndOfTransmissionMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmissionMessage

/-- Circuit Assurance Message: 6 bytes -/
structure CircuitAssuranceMessage where
  time : Alpha 6
  deriving DecidableEq, Repr

namespace CircuitAssuranceMessage

def encode (message : CircuitAssuranceMessage) : List UInt8 :=
  Alpha.encode message.time

def decode (bytes : List UInt8) : Option (CircuitAssuranceMessage × List UInt8) := do
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ time }, bytes)

@[simp] theorem encode_length (message : CircuitAssuranceMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CircuitAssuranceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CircuitAssuranceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CircuitAssuranceMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | futureOptionsTradeMessage (message : FutureOptionsTradeMessage) -- "CB" 0x4342
  | futuresTradeMessage (message : FuturesTradeMessage) -- "CF" 0x4346
  | strategyTradeMessage (message : StrategyTradeMessage) -- "CS" 0x4353
  | swapFutureTradeMessage (message : SwapFutureTradeMessage) -- "CW" 0x4357
  | optionRfqMessage (message : OptionRfqMessage) -- "D " 0x4420
  | futureOptionsRfqMessage (message : FutureOptionsRfqMessage) -- "DB" 0x4442
  | futuresRfqMessage (message : FuturesRfqMessage) -- "DF" 0x4446
  | strategyRfqMessage (message : StrategyRfqMessage) -- "DS" 0x4453
  | swapFutureRfqMessage (message : SwapFutureRfqMessage) -- "DW" 0x4457
  | instrumentScheduleNoticeOptionMessage (message : InstrumentScheduleNoticeOptionMessage) -- "E " 0x4520
  | instrumentScheduleNoticeFuturesOptionMessage (message : InstrumentScheduleNoticeFuturesOptionMessage) -- "EB" 0x4542
  | instrumentScheduleNoticeFutureMessage (message : InstrumentScheduleNoticeFutureMessage) -- "EF" 0x4546
  | instrumentScheduleNoticeStrategyMessage (message : InstrumentScheduleNoticeStrategyMessage) -- "ES" 0x4553
  | instrumentScheduleNoticeSwapFutureMessage (message : InstrumentScheduleNoticeSwapFutureMessage) -- "EW" 0x4557
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | futureOptionsQuoteMessage (message : FutureOptionsQuoteMessage) -- "FB" 0x4642
  | futuresQuoteMessage (message : FuturesQuoteMessage) -- "FF" 0x4646
  | strategyQuoteMessage (message : StrategyQuoteMessage) -- "FS" 0x4653
  | swapFutureQuoteMessage (message : SwapFutureQuoteMessage) -- "FW" 0x4657
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | futureOptionsMarketDepthMessage (message : FutureOptionsMarketDepthMessage) -- "HB" 0x4842
  | futuresMarketDepthMessage (message : FuturesMarketDepthMessage) -- "HF" 0x4846
  | strategyMarketDepthMessage (message : StrategyMarketDepthMessage) -- "HS" 0x4853
  | swapFutureMarketDepthMessage (message : SwapFutureMarketDepthMessage) -- "HW" 0x4857
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | futureOptionsTradeCancellationMessage (message : FutureOptionsTradeCancellationMessage) -- "IB" 0x4942
  | futuresTradeCancellationMessage (message : FuturesTradeCancellationMessage) -- "IF" 0x4946
  | strategyTradeCancellationMessage (message : StrategyTradeCancellationMessage) -- "IS" 0x4953
  | swapFutureTradeCancellationMessage (message : SwapFutureTradeCancellationMessage) -- "IW" 0x4957
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | futureOptionsInstrumentKeysMessage (message : FutureOptionsInstrumentKeysMessage) -- "JB" 0x4A42
  | underlyingInstrumentKeysMessage (message : UnderlyingInstrumentKeysMessage) -- "JE" 0x4A45
  | futuresInstrumentKeysMessage (message : FuturesInstrumentKeysMessage) -- "JF" 0x4A46
  | strategyInstrumentKeysMessage (message : StrategyInstrumentKeysMessage) -- "JS" 0x4A53
  | swapFutureInstrumentKeysMessage (message : SwapFutureInstrumentKeysMessage) -- "JW" 0x4A57
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | futureOptionsSummaryMessage (message : FutureOptionsSummaryMessage) -- "NB" 0x4E42
  | futuresSummaryMessage (message : FuturesSummaryMessage) -- "NF" 0x4E46
  | strategySummaryMessage (message : StrategySummaryMessage) -- "NS" 0x4E53
  | swapFutureSummaryMessage (message : SwapFutureSummaryMessage) -- "NW" 0x4E57
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfFutureOptionsSummaryMessage (message : BeginningOfFutureOptionsSummaryMessage) -- "QB" 0x5142
  | beginningOfFuturesSummaryMessage (message : BeginningOfFuturesSummaryMessage) -- "QF" 0x5146
  | beginningOfStrategySummaryMessage (message : BeginningOfStrategySummaryMessage) -- "QS" 0x5153
  | swapFutureBeginningOfSummaryMessage (message : SwapFutureBeginningOfSummaryMessage) -- "QW" 0x5157
  | optionTradeCorrectionMessage (message : OptionTradeCorrectionMessage) -- "X " 0x5820
  | futureOptionsTradeCorrectionMessage (message : FutureOptionsTradeCorrectionMessage) -- "XB" 0x5842
  | futuresTradeCorrectionMessage (message : FuturesTradeCorrectionMessage) -- "XF" 0x5846
  | strategyTradeCorrectionMessage (message : StrategyTradeCorrectionMessage) -- "XS" 0x5853
  | swapFutureTradeCorrectionMessage (message : SwapFutureTradeCorrectionMessage) -- "XW" 0x5857
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | strategiesMessage (message : StrategiesMessage) -- "GS" 0x4753
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | tickTableMessage (message : TickTableMessage) -- "TT" 0x5454
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .optionTradeMessage _ => 17184
  | .futureOptionsTradeMessage _ => 17218
  | .futuresTradeMessage _ => 17222
  | .strategyTradeMessage _ => 17235
  | .swapFutureTradeMessage _ => 17239
  | .optionRfqMessage _ => 17440
  | .futureOptionsRfqMessage _ => 17474
  | .futuresRfqMessage _ => 17478
  | .strategyRfqMessage _ => 17491
  | .swapFutureRfqMessage _ => 17495
  | .instrumentScheduleNoticeOptionMessage _ => 17696
  | .instrumentScheduleNoticeFuturesOptionMessage _ => 17730
  | .instrumentScheduleNoticeFutureMessage _ => 17734
  | .instrumentScheduleNoticeStrategyMessage _ => 17747
  | .instrumentScheduleNoticeSwapFutureMessage _ => 17751
  | .optionQuoteMessage _ => 17952
  | .futureOptionsQuoteMessage _ => 17986
  | .futuresQuoteMessage _ => 17990
  | .strategyQuoteMessage _ => 18003
  | .swapFutureQuoteMessage _ => 18007
  | .optionMarketDepthMessage _ => 18464
  | .futureOptionsMarketDepthMessage _ => 18498
  | .futuresMarketDepthMessage _ => 18502
  | .strategyMarketDepthMessage _ => 18515
  | .swapFutureMarketDepthMessage _ => 18519
  | .optionTradeCancellationMessage _ => 18720
  | .futureOptionsTradeCancellationMessage _ => 18754
  | .futuresTradeCancellationMessage _ => 18758
  | .strategyTradeCancellationMessage _ => 18771
  | .swapFutureTradeCancellationMessage _ => 18775
  | .optionInstrumentKeysMessage _ => 18976
  | .futureOptionsInstrumentKeysMessage _ => 19010
  | .underlyingInstrumentKeysMessage _ => 19013
  | .futuresInstrumentKeysMessage _ => 19014
  | .strategyInstrumentKeysMessage _ => 19027
  | .swapFutureInstrumentKeysMessage _ => 19031
  | .optionSummaryMessage _ => 20000
  | .futureOptionsSummaryMessage _ => 20034
  | .futuresSummaryMessage _ => 20038
  | .strategySummaryMessage _ => 20051
  | .swapFutureSummaryMessage _ => 20055
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfFutureOptionsSummaryMessage _ => 20802
  | .beginningOfFuturesSummaryMessage _ => 20806
  | .beginningOfStrategySummaryMessage _ => 20819
  | .swapFutureBeginningOfSummaryMessage _ => 20823
  | .optionTradeCorrectionMessage _ => 22560
  | .futureOptionsTradeCorrectionMessage _ => 22594
  | .futuresTradeCorrectionMessage _ => 22598
  | .strategyTradeCorrectionMessage _ => 22611
  | .swapFutureTradeCorrectionMessage _ => 22615
  | .groupStatusMessage _ => 18258
  | .strategiesMessage _ => 18259
  | .bulletinsMessage _ => 19488
  | .endOfSalesMessage _ => 21280
  | .tickTableMessage _ => 21588
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048

def encode : MessageBody → List UInt8
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .futureOptionsTradeMessage message => FutureOptionsTradeMessage.encode message
  | .futuresTradeMessage message => FuturesTradeMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .swapFutureTradeMessage message => SwapFutureTradeMessage.encode message
  | .optionRfqMessage message => OptionRfqMessage.encode message
  | .futureOptionsRfqMessage message => FutureOptionsRfqMessage.encode message
  | .futuresRfqMessage message => FuturesRfqMessage.encode message
  | .strategyRfqMessage message => StrategyRfqMessage.encode message
  | .swapFutureRfqMessage message => SwapFutureRfqMessage.encode message
  | .instrumentScheduleNoticeOptionMessage message => InstrumentScheduleNoticeOptionMessage.encode message
  | .instrumentScheduleNoticeFuturesOptionMessage message => InstrumentScheduleNoticeFuturesOptionMessage.encode message
  | .instrumentScheduleNoticeFutureMessage message => InstrumentScheduleNoticeFutureMessage.encode message
  | .instrumentScheduleNoticeStrategyMessage message => InstrumentScheduleNoticeStrategyMessage.encode message
  | .instrumentScheduleNoticeSwapFutureMessage message => InstrumentScheduleNoticeSwapFutureMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .futureOptionsQuoteMessage message => FutureOptionsQuoteMessage.encode message
  | .futuresQuoteMessage message => FuturesQuoteMessage.encode message
  | .strategyQuoteMessage message => StrategyQuoteMessage.encode message
  | .swapFutureQuoteMessage message => SwapFutureQuoteMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .futureOptionsMarketDepthMessage message => FutureOptionsMarketDepthMessage.encode message
  | .futuresMarketDepthMessage message => FuturesMarketDepthMessage.encode message
  | .strategyMarketDepthMessage message => StrategyMarketDepthMessage.encode message
  | .swapFutureMarketDepthMessage message => SwapFutureMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .futureOptionsTradeCancellationMessage message => FutureOptionsTradeCancellationMessage.encode message
  | .futuresTradeCancellationMessage message => FuturesTradeCancellationMessage.encode message
  | .strategyTradeCancellationMessage message => StrategyTradeCancellationMessage.encode message
  | .swapFutureTradeCancellationMessage message => SwapFutureTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .futureOptionsInstrumentKeysMessage message => FutureOptionsInstrumentKeysMessage.encode message
  | .underlyingInstrumentKeysMessage message => UnderlyingInstrumentKeysMessage.encode message
  | .futuresInstrumentKeysMessage message => FuturesInstrumentKeysMessage.encode message
  | .strategyInstrumentKeysMessage message => StrategyInstrumentKeysMessage.encode message
  | .swapFutureInstrumentKeysMessage message => SwapFutureInstrumentKeysMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .futureOptionsSummaryMessage message => FutureOptionsSummaryMessage.encode message
  | .futuresSummaryMessage message => FuturesSummaryMessage.encode message
  | .strategySummaryMessage message => StrategySummaryMessage.encode message
  | .swapFutureSummaryMessage message => SwapFutureSummaryMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfFutureOptionsSummaryMessage message => BeginningOfFutureOptionsSummaryMessage.encode message
  | .beginningOfFuturesSummaryMessage message => BeginningOfFuturesSummaryMessage.encode message
  | .beginningOfStrategySummaryMessage message => BeginningOfStrategySummaryMessage.encode message
  | .swapFutureBeginningOfSummaryMessage message => SwapFutureBeginningOfSummaryMessage.encode message
  | .optionTradeCorrectionMessage message => OptionTradeCorrectionMessage.encode message
  | .futureOptionsTradeCorrectionMessage message => FutureOptionsTradeCorrectionMessage.encode message
  | .futuresTradeCorrectionMessage message => FuturesTradeCorrectionMessage.encode message
  | .strategyTradeCorrectionMessage message => StrategyTradeCorrectionMessage.encode message
  | .swapFutureTradeCorrectionMessage message => SwapFutureTradeCorrectionMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .strategiesMessage message => StrategiesMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .tickTableMessage message => TickTableMessage.encode message
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3375 := by
  cases message with
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
  | swapFutureTradeMessage inner =>
    simp only [encode, SwapFutureTradeMessage.encode_length]
    omega
  | optionRfqMessage inner =>
    simp only [encode, OptionRfqMessage.encode_length]
    omega
  | futureOptionsRfqMessage inner =>
    simp only [encode, FutureOptionsRfqMessage.encode_length]
    omega
  | futuresRfqMessage inner =>
    simp only [encode, FuturesRfqMessage.encode_length]
    omega
  | strategyRfqMessage inner =>
    simp only [encode, StrategyRfqMessage.encode_length]
    omega
  | swapFutureRfqMessage inner =>
    simp only [encode, SwapFutureRfqMessage.encode_length]
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
  | instrumentScheduleNoticeSwapFutureMessage inner =>
    simp only [encode, InstrumentScheduleNoticeSwapFutureMessage.encode_length]
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
  | swapFutureQuoteMessage inner =>
    simp only [encode, SwapFutureQuoteMessage.encode_length]
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
  | swapFutureMarketDepthMessage inner =>
    have bound_inner := SwapFutureMarketDepthMessage.encode_length_le inner
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
  | swapFutureTradeCancellationMessage inner =>
    simp only [encode, SwapFutureTradeCancellationMessage.encode_length]
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
    simp only [encode, StrategyInstrumentKeysMessage.encode_length]
    omega
  | swapFutureInstrumentKeysMessage inner =>
    simp only [encode, SwapFutureInstrumentKeysMessage.encode_length]
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
    have bound_inner := StrategySummaryMessage.encode_length_le inner
    simp only [encode]
    omega
  | swapFutureSummaryMessage inner =>
    simp only [encode, SwapFutureSummaryMessage.encode_length]
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
  | swapFutureBeginningOfSummaryMessage inner =>
    simp only [encode, SwapFutureBeginningOfSummaryMessage.encode_length]
    omega
  | optionTradeCorrectionMessage inner =>
    simp only [encode, OptionTradeCorrectionMessage.encode_length]
    omega
  | futureOptionsTradeCorrectionMessage inner =>
    simp only [encode, FutureOptionsTradeCorrectionMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [encode, FuturesTradeCorrectionMessage.encode_length]
    omega
  | strategyTradeCorrectionMessage inner =>
    simp only [encode, StrategyTradeCorrectionMessage.encode_length]
    omega
  | swapFutureTradeCorrectionMessage inner =>
    simp only [encode, SwapFutureTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | strategiesMessage inner =>
    simp only [encode, StrategiesMessage.encode_length]
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
  if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17218 then (FutureOptionsTradeMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeMessage message, rest)
  else if tag = 17222 then (FuturesTradeMessage.decode bytes).map fun (message, rest) => (.futuresTradeMessage message, rest)
  else if tag = 17235 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 17239 then (SwapFutureTradeMessage.decode bytes).map fun (message, rest) => (.swapFutureTradeMessage message, rest)
  else if tag = 17440 then (OptionRfqMessage.decode bytes).map fun (message, rest) => (.optionRfqMessage message, rest)
  else if tag = 17474 then (FutureOptionsRfqMessage.decode bytes).map fun (message, rest) => (.futureOptionsRfqMessage message, rest)
  else if tag = 17478 then (FuturesRfqMessage.decode bytes).map fun (message, rest) => (.futuresRfqMessage message, rest)
  else if tag = 17491 then (StrategyRfqMessage.decode bytes).map fun (message, rest) => (.strategyRfqMessage message, rest)
  else if tag = 17495 then (SwapFutureRfqMessage.decode bytes).map fun (message, rest) => (.swapFutureRfqMessage message, rest)
  else if tag = 17696 then (InstrumentScheduleNoticeOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeOptionMessage message, rest)
  else if tag = 17730 then (InstrumentScheduleNoticeFuturesOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFuturesOptionMessage message, rest)
  else if tag = 17734 then (InstrumentScheduleNoticeFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFutureMessage message, rest)
  else if tag = 17747 then (InstrumentScheduleNoticeStrategyMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeStrategyMessage message, rest)
  else if tag = 17751 then (InstrumentScheduleNoticeSwapFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeSwapFutureMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 17986 then (FutureOptionsQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsQuoteMessage message, rest)
  else if tag = 17990 then (FuturesQuoteMessage.decode bytes).map fun (message, rest) => (.futuresQuoteMessage message, rest)
  else if tag = 18003 then (StrategyQuoteMessage.decode bytes).map fun (message, rest) => (.strategyQuoteMessage message, rest)
  else if tag = 18007 then (SwapFutureQuoteMessage.decode bytes).map fun (message, rest) => (.swapFutureQuoteMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18498 then (FutureOptionsMarketDepthMessage.decode bytes).map fun (message, rest) => (.futureOptionsMarketDepthMessage message, rest)
  else if tag = 18502 then (FuturesMarketDepthMessage.decode bytes).map fun (message, rest) => (.futuresMarketDepthMessage message, rest)
  else if tag = 18515 then (StrategyMarketDepthMessage.decode bytes).map fun (message, rest) => (.strategyMarketDepthMessage message, rest)
  else if tag = 18519 then (SwapFutureMarketDepthMessage.decode bytes).map fun (message, rest) => (.swapFutureMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18754 then (FutureOptionsTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCancellationMessage message, rest)
  else if tag = 18758 then (FuturesTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futuresTradeCancellationMessage message, rest)
  else if tag = 18771 then (StrategyTradeCancellationMessage.decode bytes).map fun (message, rest) => (.strategyTradeCancellationMessage message, rest)
  else if tag = 18775 then (SwapFutureTradeCancellationMessage.decode bytes).map fun (message, rest) => (.swapFutureTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19010 then (FutureOptionsInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futureOptionsInstrumentKeysMessage message, rest)
  else if tag = 19013 then (UnderlyingInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.underlyingInstrumentKeysMessage message, rest)
  else if tag = 19014 then (FuturesInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futuresInstrumentKeysMessage message, rest)
  else if tag = 19027 then (StrategyInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.strategyInstrumentKeysMessage message, rest)
  else if tag = 19031 then (SwapFutureInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.swapFutureInstrumentKeysMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20034 then (FutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.futureOptionsSummaryMessage message, rest)
  else if tag = 20038 then (FuturesSummaryMessage.decode bytes).map fun (message, rest) => (.futuresSummaryMessage message, rest)
  else if tag = 20051 then (StrategySummaryMessage.decode bytes).map fun (message, rest) => (.strategySummaryMessage message, rest)
  else if tag = 20055 then (SwapFutureSummaryMessage.decode bytes).map fun (message, rest) => (.swapFutureSummaryMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20802 then (BeginningOfFutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFutureOptionsSummaryMessage message, rest)
  else if tag = 20806 then (BeginningOfFuturesSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFuturesSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfStrategySummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfStrategySummaryMessage message, rest)
  else if tag = 20823 then (SwapFutureBeginningOfSummaryMessage.decode bytes).map fun (message, rest) => (.swapFutureBeginningOfSummaryMessage message, rest)
  else if tag = 22560 then (OptionTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.optionTradeCorrectionMessage message, rest)
  else if tag = 22594 then (FutureOptionsTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCorrectionMessage message, rest)
  else if tag = 22598 then (FuturesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futuresTradeCorrectionMessage message, rest)
  else if tag = 22611 then (StrategyTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.strategyTradeCorrectionMessage message, rest)
  else if tag = 22615 then (SwapFutureTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.swapFutureTradeCorrectionMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (StrategiesMessage.decode bytes).map fun (message, rest) => (.strategiesMessage message, rest)
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
theorem encode_length_le (message : Packet) : (encode message).length ≤ 3388 := by
  unfold encode
  cases message.messageBody with
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
  | swapFutureTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureTradeMessage.encode_length]
    omega
  | optionRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRfqMessage.encode_length]
    omega
  | futureOptionsRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsRfqMessage.encode_length]
    omega
  | futuresRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesRfqMessage.encode_length]
    omega
  | strategyRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyRfqMessage.encode_length]
    omega
  | swapFutureRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureRfqMessage.encode_length]
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
  | instrumentScheduleNoticeSwapFutureMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeSwapFutureMessage.encode_length]
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
  | swapFutureQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureQuoteMessage.encode_length]
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
  | swapFutureMarketDepthMessage inner =>
    have bound_inner := SwapFutureMarketDepthMessage.encode_length_le inner
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
  | swapFutureTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureTradeCancellationMessage.encode_length]
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
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyInstrumentKeysMessage.encode_length]
    omega
  | swapFutureInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureInstrumentKeysMessage.encode_length]
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
    have bound_inner := StrategySummaryMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | swapFutureSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureSummaryMessage.encode_length]
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
  | swapFutureBeginningOfSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureBeginningOfSummaryMessage.encode_length]
    omega
  | optionTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCorrectionMessage.encode_length]
    omega
  | futureOptionsTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCorrectionMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCorrectionMessage.encode_length]
    omega
  | strategyTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCorrectionMessage.encode_length]
    omega
  | swapFutureTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SwapFutureTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | strategiesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategiesMessage.encode_length]
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

end Omi.TmxMxSolamulticastHsvfV111
