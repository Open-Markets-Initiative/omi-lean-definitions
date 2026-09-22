import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Equity Last Sale v1.2.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesLastsaleItchV129

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x35, 0x36, 0x38, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x39, 0x41, 0x42, 0x43, 0x4F, 0x50]

inductive TradeType where
  | standardTrade -- Standard Trade
  | nonStandardSettlement -- Non Standard Settlement
  | exchangeGrantedTrade -- Exchange Granted Trade
  | portfolioTrade -- Portfolio Trade
  | volumeWeightedAveragePriceTrade -- Volume Weighted Average Price Trade
  | preOpeningTrade -- Pre Opening Trade
  | standardRoutedTrade -- Standard Routed Trade
  | standardRoutedDarkTrade -- Standard Routed Dark Trade
  | standardDarkTrade -- Standard Dark Trade
  | standardAuctionOnDemandTrade -- Standard Auction On Demand Trade
  | standardTradeAtClosingTrade -- Standard Trade At Closing Trade
  | contingentTrade -- Contingent Trade
  | otcStandardTrade -- Otc Standard Trade
  | otcNonStandardTrade -- Otc Non Standard Trade
  | siStandardTrade -- Si Standard Trade
  | siNonStandardTrade -- Si Non Standard Trade
  | otcLoanPayment -- Otc Loan Payment
  | otcPrimaryTransaction -- Otc Primary Transaction
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .standardTrade => 0x31
  | .nonStandardSettlement => 0x32
  | .exchangeGrantedTrade => 0x33
  | .portfolioTrade => 0x35
  | .volumeWeightedAveragePriceTrade => 0x36
  | .preOpeningTrade => 0x38
  | .standardRoutedTrade => 0x44
  | .standardRoutedDarkTrade => 0x45
  | .standardDarkTrade => 0x46
  | .standardAuctionOnDemandTrade => 0x47
  | .standardTradeAtClosingTrade => 0x48
  | .contingentTrade => 0x49
  | .otcStandardTrade => 0x39
  | .otcNonStandardTrade => 0x41
  | .siStandardTrade => 0x42
  | .siNonStandardTrade => 0x43
  | .otcLoanPayment => 0x4F
  | .otcPrimaryTransaction => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x31 then .standardTrade
  else if byte = 0x32 then .nonStandardSettlement
  else if byte = 0x33 then .exchangeGrantedTrade
  else if byte = 0x35 then .portfolioTrade
  else if byte = 0x36 then .volumeWeightedAveragePriceTrade
  else if byte = 0x38 then .preOpeningTrade
  else if byte = 0x44 then .standardRoutedTrade
  else if byte = 0x45 then .standardRoutedDarkTrade
  else if byte = 0x46 then .standardDarkTrade
  else if byte = 0x47 then .standardAuctionOnDemandTrade
  else if byte = 0x48 then .standardTradeAtClosingTrade
  else if byte = 0x49 then .contingentTrade
  else if byte = 0x39 then .otcStandardTrade
  else if byte = 0x41 then .otcNonStandardTrade
  else if byte = 0x42 then .siStandardTrade
  else if byte = 0x43 then .siNonStandardTrade
  else if byte = 0x4F then .otcLoanPayment
  else .otcPrimaryTransaction

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | standardTrade => decide
  | nonStandardSettlement => decide
  | exchangeGrantedTrade => decide
  | portfolioTrade => decide
  | volumeWeightedAveragePriceTrade => decide
  | preOpeningTrade => decide
  | standardRoutedTrade => decide
  | standardRoutedDarkTrade => decide
  | standardDarkTrade => decide
  | standardAuctionOnDemandTrade => decide
  | standardTradeAtClosingTrade => decide
  | contingentTrade => decide
  | otcStandardTrade => decide
  | otcNonStandardTrade => decide
  | siStandardTrade => decide
  | siNonStandardTrade => decide
  | otcLoanPayment => decide
  | otcPrimaryTransaction => decide
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

/-- Transaction To Be Cleared: one byte code -/
def TransactionToBeCleared.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TransactionToBeCleared where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionToBeCleared.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionToBeCleared

def toByte : TransactionToBeCleared → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionToBeCleared :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TransactionToBeCleared :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionToBeCleared) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionToBeCleared) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionToBeCleared × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionToBeCleared) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionToBeCleared) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionToBeCleared

/-- Adjusted Closing Price Message: 22 bytes -/
structure AdjustedClosingPriceMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderBook : BitVec 32
  adjustedClosingPrice : BitVec 64
  deriving DecidableEq, Repr

namespace AdjustedClosingPriceMessage

def encode (message : AdjustedClosingPriceMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 8 message.adjustedClosingPrice)))

def decode (bytes : List UInt8) : Option (AdjustedClosingPriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (adjustedClosingPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, trackingNumber, orderBook, adjustedClosingPrice }, bytes)

@[simp] theorem encode_length (message : AdjustedClosingPriceMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AdjustedClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdjustedClosingPriceMessage) (rest : List UInt8) :
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

end AdjustedClosingPriceMessage

/-- On Exchange Trade Message: 92 bytes -/
structure OnExchangeTradeMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderBook : BitVec 32
  executionDate : BitVec 32
  executionTime : BitVec 64
  agreementDate : BitVec 32
  agreementTime : BitVec 64
  priceOnExchange : BitVec 64
  quantity : BitVec 64
  venueOfExecution : Alpha 4
  transactionIdentifierCode : Alpha 10
  mmtTradeFlags : Alpha 14
  tradeType : TradeType
  mpidBuyer : Alpha 4
  mpidSeller : Alpha 4
  transactionToBeCleared : TransactionToBeCleared
  deriving DecidableEq, Repr

namespace OnExchangeTradeMessage

def encode (message : OnExchangeTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.executionDate
    ++ (encodeUInt 8 message.executionTime
    ++ (encodeUInt 4 message.agreementDate
    ++ (encodeUInt 8 message.agreementTime
    ++ (encodeUInt 8 message.priceOnExchange
    ++ (encodeUInt 8 message.quantity
    ++ (Alpha.encode message.venueOfExecution
    ++ (Alpha.encode message.transactionIdentifierCode
    ++ (Alpha.encode message.mmtTradeFlags
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.mpidBuyer
    ++ (Alpha.encode message.mpidSeller
    ++ (TransactionToBeCleared.encode message.transactionToBeCleared)))))))))))))))

def decode (bytes : List UInt8) : Option (OnExchangeTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (executionDate, bytes) ← decodeUInt 4 bytes
  let (executionTime, bytes) ← decodeUInt 8 bytes
  let (agreementDate, bytes) ← decodeUInt 4 bytes
  let (agreementTime, bytes) ← decodeUInt 8 bytes
  let (priceOnExchange, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (transactionIdentifierCode, bytes) ← Alpha.decode 10 bytes
  let (mmtTradeFlags, bytes) ← Alpha.decode 14 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (mpidBuyer, bytes) ← Alpha.decode 4 bytes
  let (mpidSeller, bytes) ← Alpha.decode 4 bytes
  let (transactionToBeCleared, bytes) ← TransactionToBeCleared.decode bytes
  pure ({ timestamp, trackingNumber, orderBook, executionDate, executionTime, agreementDate, agreementTime, priceOnExchange, quantity, venueOfExecution, transactionIdentifierCode, mmtTradeFlags, tradeType, mpidBuyer, mpidSeller, transactionToBeCleared }, bytes)

@[simp] theorem encode_length (message : OnExchangeTradeMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeType.encode_length, TransactionToBeCleared.encode_length]

theorem encode_length_pos (message : OnExchangeTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OnExchangeTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TransactionToBeCleared.decode_encode, some_bind]
  rfl

end OnExchangeTradeMessage

/-- Otc Trade Message: 147 bytes -/
structure OtcTradeMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  instrumentIdentificationCodeType : Alpha 4
  instrumentIdentificationCode : Alpha 12
  agreementDate : BitVec 32
  agreementTime : BitVec 64
  priceOtc : BitVec 64
  priceFraction : BitVec 8
  priceNotation : Alpha 4
  priceCurrency : Alpha 3
  quantity : BitVec 64
  quantityFraction : BitVec 8
  notationOfTheQuantityInMeasurementUnit : Alpha 25
  quantityInMeasurementUnit : BitVec 64
  quantityInMeasurementUnitFraction : BitVec 8
  venueOfExecution : Alpha 4
  notionalAmount : BitVec 64
  notionalAmountFraction : BitVec 8
  notionalCurrency : Alpha 3
  type : Alpha 4
  transactionIdentifierCode : Alpha 10
  mmtTradeFlags : Alpha 14
  transactionToBeCleared : TransactionToBeCleared
  tradeType : TradeType
  thirdCountryTradingVenueOfExecution : Alpha 4
  deriving DecidableEq, Repr

namespace OtcTradeMessage

def encode (message : OtcTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (Alpha.encode message.instrumentIdentificationCodeType
    ++ (Alpha.encode message.instrumentIdentificationCode
    ++ (encodeUInt 4 message.agreementDate
    ++ (encodeUInt 8 message.agreementTime
    ++ (encodeUInt 8 message.priceOtc
    ++ (encodeUInt 1 message.priceFraction
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.priceCurrency
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 1 message.quantityFraction
    ++ (Alpha.encode message.notationOfTheQuantityInMeasurementUnit
    ++ (encodeUInt 8 message.quantityInMeasurementUnit
    ++ (encodeUInt 1 message.quantityInMeasurementUnitFraction
    ++ (Alpha.encode message.venueOfExecution
    ++ (encodeUInt 8 message.notionalAmount
    ++ (encodeUInt 1 message.notionalAmountFraction
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.type
    ++ (Alpha.encode message.transactionIdentifierCode
    ++ (Alpha.encode message.mmtTradeFlags
    ++ (TransactionToBeCleared.encode message.transactionToBeCleared
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.thirdCountryTradingVenueOfExecution))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OtcTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (instrumentIdentificationCodeType, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdentificationCode, bytes) ← Alpha.decode 12 bytes
  let (agreementDate, bytes) ← decodeUInt 4 bytes
  let (agreementTime, bytes) ← decodeUInt 8 bytes
  let (priceOtc, bytes) ← decodeUInt 8 bytes
  let (priceFraction, bytes) ← decodeUInt 1 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (priceCurrency, bytes) ← Alpha.decode 3 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (quantityFraction, bytes) ← decodeUInt 1 bytes
  let (notationOfTheQuantityInMeasurementUnit, bytes) ← Alpha.decode 25 bytes
  let (quantityInMeasurementUnit, bytes) ← decodeUInt 8 bytes
  let (quantityInMeasurementUnitFraction, bytes) ← decodeUInt 1 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (notionalAmount, bytes) ← decodeUInt 8 bytes
  let (notionalAmountFraction, bytes) ← decodeUInt 1 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (type, bytes) ← Alpha.decode 4 bytes
  let (transactionIdentifierCode, bytes) ← Alpha.decode 10 bytes
  let (mmtTradeFlags, bytes) ← Alpha.decode 14 bytes
  let (transactionToBeCleared, bytes) ← TransactionToBeCleared.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (thirdCountryTradingVenueOfExecution, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, instrumentIdentificationCodeType, instrumentIdentificationCode, agreementDate, agreementTime, priceOtc, priceFraction, priceNotation, priceCurrency, quantity, quantityFraction, notationOfTheQuantityInMeasurementUnit, quantityInMeasurementUnit, quantityInMeasurementUnitFraction, venueOfExecution, notionalAmount, notionalAmountFraction, notionalCurrency, type, transactionIdentifierCode, mmtTradeFlags, transactionToBeCleared, tradeType, thirdCountryTradingVenueOfExecution }, bytes)

@[simp] theorem encode_length (message : OtcTradeMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TransactionToBeCleared.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : OtcTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OtcTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionToBeCleared.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OtcTradeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | adjustedClosingPriceMessage (message : AdjustedClosingPriceMessage) -- "G" 0x47
  | onExchangeTradeMessage (message : OnExchangeTradeMessage) -- "T" 0x54
  | otcTradeMessage (message : OtcTradeMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .adjustedClosingPriceMessage _ => 71
  | .onExchangeTradeMessage _ => 84
  | .otcTradeMessage _ => 90

def encode : Payload → List UInt8
  | .adjustedClosingPriceMessage message => AdjustedClosingPriceMessage.encode message
  | .onExchangeTradeMessage message => OnExchangeTradeMessage.encode message
  | .otcTradeMessage message => OtcTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 147 := by
  cases message with
  | adjustedClosingPriceMessage inner =>
    simp only [encode, AdjustedClosingPriceMessage.encode_length]
    omega
  | onExchangeTradeMessage inner =>
    simp only [encode, OnExchangeTradeMessage.encode_length]
    omega
  | otcTradeMessage inner =>
    simp only [encode, OtcTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 71 then (AdjustedClosingPriceMessage.decode bytes).map fun (message, rest) => (.adjustedClosingPriceMessage message, rest)
  else if tag = 84 then (OnExchangeTradeMessage.decode bytes).map fun (message, rest) => (.onExchangeTradeMessage message, rest)
  else if tag = 90 then (OtcTradeMessage.decode bytes).map fun (message, rest) => (.otcTradeMessage message, rest)
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
  | adjustedClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AdjustedClosingPriceMessage.encode_length]
    omega
  | onExchangeTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OnExchangeTradeMessage.encode_length]
    omega
  | otcTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OtcTradeMessage.encode_length]
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

end Omi.NasdaqNordicequitiesLastsaleItchV129
