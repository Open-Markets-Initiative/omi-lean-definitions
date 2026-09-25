import Omi.Wire

/-!
# Box Options Market Sola Trade Reporting v4.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BoxBoxoptionsSolatradereportingAtrV45Server

/-- Message Flag: one byte code -/
def MessageFlag.codes : List UInt8 :=
  [0x52, 0x44]

inductive MessageFlag where
  | retransmittedMessage -- Retransmitted Message
  | duplicatedMessage -- Duplicated Message
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageFlag

def toByte : MessageFlag → UInt8
  | .retransmittedMessage => 0x52
  | .duplicatedMessage => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageFlag :=
  if byte = 0x52 then .retransmittedMessage
  else .duplicatedMessage

def ofByte (byte : UInt8) : MessageFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageFlag) : ofByte value.toByte = value := by
  cases value with
  | retransmittedMessage => decide
  | duplicatedMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MessageFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageFlag

/-- Transaction Type: one byte code -/
def TransactionType.codes : List UInt8 :=
  [0x42, 0x53]

inductive TransactionType where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionType

def toByte : TransactionType → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionType :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : TransactionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionType) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50]

inductive OptionType where
  | call -- Call
  | putBlankIfNotAnOption -- Put Blank If Not An Option
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .putBlankIfNotAnOption => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else .putBlankIfNotAnOption

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | putBlankIfNotAnOption => decide
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

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x36, 0x37, 0x38, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive AccountType where
  | publicCustomer -- Public Customer
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | floorBrokerCustomer -- Floor Broker Customer
  | brokerDealerClearedAsCustomer -- Broker Dealer Cleared As Customer
  | awayMarketMaker -- Away Market Maker
  | floorBrokerDealer -- Floor Broker Dealer
  | floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing -- Floor Market Maker Flex Symbology Symbol Is Prefixed By One Of The Following
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .publicCustomer => 0x36
  | .brokerDealer => 0x37
  | .marketMaker => 0x38
  | .professionalCustomer => 0x54
  | .floorBrokerCustomer => 0x56
  | .brokerDealerClearedAsCustomer => 0x57
  | .awayMarketMaker => 0x58
  | .floorBrokerDealer => 0x59
  | .floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x36 then .publicCustomer
  else if byte = 0x37 then .brokerDealer
  else if byte = 0x38 then .marketMaker
  else if byte = 0x54 then .professionalCustomer
  else if byte = 0x56 then .floorBrokerCustomer
  else if byte = 0x57 then .brokerDealerClearedAsCustomer
  else if byte = 0x58 then .awayMarketMaker
  else if byte = 0x59 then .floorBrokerDealer
  else .floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | publicCustomer => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | floorBrokerCustomer => decide
  | brokerDealerClearedAsCustomer => decide
  | awayMarketMaker => decide
  | floorBrokerDealer => decide
  | floorMarketMakerFlexSymbologySymbolIsPrefixedByOneOfTheFollowing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Liquidity Status: one byte code -/
def LiquidityStatus.codes : List UInt8 :=
  [0x4D, 0x54]

inductive LiquidityStatus where
  | maker -- Maker
  | taker -- Taker
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityStatus

def toByte : LiquidityStatus → UInt8
  | .maker => 0x4D
  | .taker => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityStatus :=
  if byte = 0x4D then .maker
  else .taker

def ofByte (byte : UInt8) : LiquidityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityStatus) : ofByte value.toByte = value := by
  cases value with
  | maker => decide
  | taker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityStatus

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x4F, 0x54, 0x4D, 0x50, 0x46, 0x41, 0x45, 0x53, 0x49, 0x52, 0x43]

inductive TradeType where
  | crossedOrdersATradeWithTheSameFirmIdOnBothSides -- Crossed Orders A Trade With The Same Firm Id On Both Sides
  | traderCrossedOrdersATradeWithTheSameTraderIdOnBothSides -- Trader Crossed Orders A Trade With The Same Trader Id On Both Sides
  | tprTradeATradeDoneByAThirdPartyRouter -- Tpr Trade A Trade Done By A Third Party Router
  | pipATradeDoneAtTheEndOfAPipAuction -- Pip A Trade Done At The End Of A Pip Auction
  | firmDoATradeResultingFromADirectedOrder -- Firm Do A Trade Resulting From A Directed Order
  | asOfATradeEnteredByTheBoxMocToCorrectATradeExecutedOnAPreviousDay -- As Of A Trade Entered By The Box Moc To Correct A Trade Executed On A Previous Day
  | lateATradeEnteredByTheBoxMocToCorrectATradeExecutedOnTheSameDay -- Late A Trade Entered By The Box Moc To Correct A Trade Executed On The Same Day
  | solicitationATradeDoneAsPartOfASolicitationAuction -- Solicitation A Trade Done As Part Of A Solicitation Auction
  | facilitationATradeDoneAsPartOfAFacilitationAuction -- Facilitation A Trade Done As Part Of A Facilitation Auction
  | floorTrade -- Floor Trade
  | customerCrossOrdersOrQualifiedContingentCrossOrders -- Customer Cross Orders Or Qualified Contingent Cross Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .crossedOrdersATradeWithTheSameFirmIdOnBothSides => 0x4F
  | .traderCrossedOrdersATradeWithTheSameTraderIdOnBothSides => 0x54
  | .tprTradeATradeDoneByAThirdPartyRouter => 0x4D
  | .pipATradeDoneAtTheEndOfAPipAuction => 0x50
  | .firmDoATradeResultingFromADirectedOrder => 0x46
  | .asOfATradeEnteredByTheBoxMocToCorrectATradeExecutedOnAPreviousDay => 0x41
  | .lateATradeEnteredByTheBoxMocToCorrectATradeExecutedOnTheSameDay => 0x45
  | .solicitationATradeDoneAsPartOfASolicitationAuction => 0x53
  | .facilitationATradeDoneAsPartOfAFacilitationAuction => 0x49
  | .floorTrade => 0x52
  | .customerCrossOrdersOrQualifiedContingentCrossOrders => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x4F then .crossedOrdersATradeWithTheSameFirmIdOnBothSides
  else if byte = 0x54 then .traderCrossedOrdersATradeWithTheSameTraderIdOnBothSides
  else if byte = 0x4D then .tprTradeATradeDoneByAThirdPartyRouter
  else if byte = 0x50 then .pipATradeDoneAtTheEndOfAPipAuction
  else if byte = 0x46 then .firmDoATradeResultingFromADirectedOrder
  else if byte = 0x41 then .asOfATradeEnteredByTheBoxMocToCorrectATradeExecutedOnAPreviousDay
  else if byte = 0x45 then .lateATradeEnteredByTheBoxMocToCorrectATradeExecutedOnTheSameDay
  else if byte = 0x53 then .solicitationATradeDoneAsPartOfASolicitationAuction
  else if byte = 0x49 then .facilitationATradeDoneAsPartOfAFacilitationAuction
  else if byte = 0x52 then .floorTrade
  else .customerCrossOrdersOrQualifiedContingentCrossOrders

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | crossedOrdersATradeWithTheSameFirmIdOnBothSides => decide
  | traderCrossedOrdersATradeWithTheSameTraderIdOnBothSides => decide
  | tprTradeATradeDoneByAThirdPartyRouter => decide
  | pipATradeDoneAtTheEndOfAPipAuction => decide
  | firmDoATradeResultingFromADirectedOrder => decide
  | asOfATradeEnteredByTheBoxMocToCorrectATradeExecutedOnAPreviousDay => decide
  | lateATradeEnteredByTheBoxMocToCorrectATradeExecutedOnTheSameDay => decide
  | solicitationATradeDoneAsPartOfASolicitationAuction => decide
  | facilitationATradeDoneAsPartOfAFacilitationAuction => decide
  | floorTrade => decide
  | customerCrossOrdersOrQualifiedContingentCrossOrders => decide
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

/-- Opposite Account Type: one byte code -/
def OppositeAccountType.codes : List UInt8 :=
  [0x36, 0x37, 0x38, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive OppositeAccountType where
  | publicCustomer -- Public Customer
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | floorBrokerCustomer -- Floor Broker Customer
  | brokerDealerClearedAsCustomer -- Broker Dealer Cleared As Customer
  | awayMarketMaker -- Away Market Maker
  | floorBrokerDealer -- Floor Broker Dealer
  | floorMarketMaker -- Floor Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ OppositeAccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OppositeAccountType

def toByte : OppositeAccountType → UInt8
  | .publicCustomer => 0x36
  | .brokerDealer => 0x37
  | .marketMaker => 0x38
  | .professionalCustomer => 0x54
  | .floorBrokerCustomer => 0x56
  | .brokerDealerClearedAsCustomer => 0x57
  | .awayMarketMaker => 0x58
  | .floorBrokerDealer => 0x59
  | .floorMarketMaker => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OppositeAccountType :=
  if byte = 0x36 then .publicCustomer
  else if byte = 0x37 then .brokerDealer
  else if byte = 0x38 then .marketMaker
  else if byte = 0x54 then .professionalCustomer
  else if byte = 0x56 then .floorBrokerCustomer
  else if byte = 0x57 then .brokerDealerClearedAsCustomer
  else if byte = 0x58 then .awayMarketMaker
  else if byte = 0x59 then .floorBrokerDealer
  else .floorMarketMaker

def ofByte (byte : UInt8) : OppositeAccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OppositeAccountType) : ofByte value.toByte = value := by
  cases value with
  | publicCustomer => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | floorBrokerCustomer => decide
  | brokerDealerClearedAsCustomer => decide
  | awayMarketMaker => decide
  | floorBrokerDealer => decide
  | floorMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OppositeAccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OppositeAccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OppositeAccountType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OppositeAccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OppositeAccountType

/-- Start Of Day: 0 bytes -/
structure StartOfDay where
  deriving DecidableEq, Repr

namespace StartOfDay

def encode (_ : StartOfDay) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfDay × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfDay) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfDay) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfDay

/-- Circuit Assurance: 0 bytes -/
structure CircuitAssurance where
  deriving DecidableEq, Repr

namespace CircuitAssurance

def encode (_ : CircuitAssurance) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (CircuitAssurance × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : CircuitAssurance) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : CircuitAssurance) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end CircuitAssurance

/-- Restart Accepted: 0 bytes -/
structure RestartAccepted where
  deriving DecidableEq, Repr

namespace RestartAccepted

def encode (_ : RestartAccepted) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (RestartAccepted × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : RestartAccepted) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RestartAccepted) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end RestartAccepted

/-- End Of Trading: 0 bytes -/
structure EndOfTrading where
  deriving DecidableEq, Repr

namespace EndOfTrading

def encode (_ : EndOfTrading) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfTrading × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfTrading) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfTrading) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfTrading

/-- Client Signon Acknowledgment: 8 bytes -/
structure ClientSignonAcknowledgment where
  lastUserSequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace ClientSignonAcknowledgment

def encode (message : ClientSignonAcknowledgment) : List UInt8 :=
  Alpha.encode message.lastUserSequenceNumber

def decode (bytes : List UInt8) : Option (ClientSignonAcknowledgment × List UInt8) := do
  let (lastUserSequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ lastUserSequenceNumber }, bytes)

@[simp] theorem encode_length (message : ClientSignonAcknowledgment) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClientSignonAcknowledgment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClientSignonAcknowledgment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClientSignonAcknowledgment

/-- Trade: 200 bytes -/
structure Trade where
  tradeNumber : Alpha 15
  transactionType : TransactionType
  timestamp : Alpha 6
  symbol : Alpha 30
  expirationDate : Alpha 6
  strikePrice : Alpha 8
  strikePriceFractionIndicator : Alpha 1
  optionType : OptionType
  volume : Alpha 8
  priceX10000 : Alpha 8
  cmtaBroker : Alpha 4
  accountType : AccountType
  subtraderId : Alpha 3
  openClose : OpenClose
  executingBroker : Alpha 4
  clientAccountNumber : Alpha 12
  clientOrderId : Alpha 20
  clientMemo : Alpha 16
  liquidityStatus : LiquidityStatus
  tradeType : TradeType
  oppositeAccountType : OppositeAccountType
  participantSessionName : Alpha 12
  uniqueTransactionId : Alpha 10
  parentTransactionId : Alpha 10
  oppositeExecutingBroker : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace Trade

def encode (message : Trade) : List UInt8 :=
  Alpha.encode message.tradeNumber
    ++ (TransactionType.encode message.transactionType
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.priceX10000
    ++ (Alpha.encode message.cmtaBroker
    ++ (AccountType.encode message.accountType
    ++ (Alpha.encode message.subtraderId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clientMemo
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (TradeType.encode message.tradeType
    ++ (OppositeAccountType.encode message.oppositeAccountType
    ++ (Alpha.encode message.participantSessionName
    ++ (Alpha.encode message.uniqueTransactionId
    ++ (Alpha.encode message.parentTransactionId
    ++ (Alpha.encode message.oppositeExecutingBroker
    ++ (Alpha.encode message.additionalClientMemo)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (Trade × List UInt8) := do
  let (tradeNumber, bytes) ← Alpha.decode 15 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (expirationDate, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← Alpha.decode 8 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceX10000, bytes) ← Alpha.decode 8 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (oppositeAccountType, bytes) ← OppositeAccountType.decode bytes
  let (participantSessionName, bytes) ← Alpha.decode 12 bytes
  let (uniqueTransactionId, bytes) ← Alpha.decode 10 bytes
  let (parentTransactionId, bytes) ← Alpha.decode 10 bytes
  let (oppositeExecutingBroker, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ tradeNumber, transactionType, timestamp, symbol, expirationDate, strikePrice, strikePriceFractionIndicator, optionType, volume, priceX10000, cmtaBroker, accountType, subtraderId, openClose, executingBroker, clientAccountNumber, clientOrderId, clientMemo, liquidityStatus, tradeType, oppositeAccountType, participantSessionName, uniqueTransactionId, parentTransactionId, oppositeExecutingBroker, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : Trade) : (encode message).length = 200 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TransactionType.encode_length, OptionType.encode_length, AccountType.encode_length, OpenClose.encode_length, LiquidityStatus.encode_length, TradeType.encode_length, OppositeAccountType.encode_length]

theorem encode_length_pos (message : Trade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : Trade) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeAccountType.decode_encode, some_bind]
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

end Trade

/-- Trade Cancel: 200 bytes -/
structure TradeCancel where
  tradeNumber : Alpha 15
  transactionType : TransactionType
  timestamp : Alpha 6
  symbol : Alpha 30
  expirationDate : Alpha 6
  strikePrice : Alpha 8
  strikePriceFractionIndicator : Alpha 1
  optionType : OptionType
  volume : Alpha 8
  priceX10000 : Alpha 8
  cmtaBroker : Alpha 4
  accountType : AccountType
  subtraderId : Alpha 3
  openClose : OpenClose
  executingBroker : Alpha 4
  clientAccountNumber : Alpha 12
  clientOrderId : Alpha 20
  clientMemo : Alpha 16
  liquidityStatus : LiquidityStatus
  tradeType : TradeType
  oppositeAccountType : OppositeAccountType
  participantSessionName : Alpha 12
  uniqueTransactionId : Alpha 10
  parentTransactionId : Alpha 10
  oppositeExecutingBroker : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace TradeCancel

def encode (message : TradeCancel) : List UInt8 :=
  Alpha.encode message.tradeNumber
    ++ (TransactionType.encode message.transactionType
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.priceX10000
    ++ (Alpha.encode message.cmtaBroker
    ++ (AccountType.encode message.accountType
    ++ (Alpha.encode message.subtraderId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clientMemo
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (TradeType.encode message.tradeType
    ++ (OppositeAccountType.encode message.oppositeAccountType
    ++ (Alpha.encode message.participantSessionName
    ++ (Alpha.encode message.uniqueTransactionId
    ++ (Alpha.encode message.parentTransactionId
    ++ (Alpha.encode message.oppositeExecutingBroker
    ++ (Alpha.encode message.additionalClientMemo)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCancel × List UInt8) := do
  let (tradeNumber, bytes) ← Alpha.decode 15 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (expirationDate, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← Alpha.decode 8 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceX10000, bytes) ← Alpha.decode 8 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (oppositeAccountType, bytes) ← OppositeAccountType.decode bytes
  let (participantSessionName, bytes) ← Alpha.decode 12 bytes
  let (uniqueTransactionId, bytes) ← Alpha.decode 10 bytes
  let (parentTransactionId, bytes) ← Alpha.decode 10 bytes
  let (oppositeExecutingBroker, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ tradeNumber, transactionType, timestamp, symbol, expirationDate, strikePrice, strikePriceFractionIndicator, optionType, volume, priceX10000, cmtaBroker, accountType, subtraderId, openClose, executingBroker, clientAccountNumber, clientOrderId, clientMemo, liquidityStatus, tradeType, oppositeAccountType, participantSessionName, uniqueTransactionId, parentTransactionId, oppositeExecutingBroker, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : TradeCancel) : (encode message).length = 200 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TransactionType.encode_length, OptionType.encode_length, AccountType.encode_length, OpenClose.encode_length, LiquidityStatus.encode_length, TradeType.encode_length, OppositeAccountType.encode_length]

theorem encode_length_pos (message : TradeCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeAccountType.decode_encode, some_bind]
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

end TradeCancel

/-- Allocation: 200 bytes -/
structure Allocation where
  tradeNumber : Alpha 15
  transactionType : TransactionType
  timestamp : Alpha 6
  symbol : Alpha 30
  expirationDate : Alpha 6
  strikePrice : Alpha 8
  strikePriceFractionIndicator : Alpha 1
  optionType : OptionType
  volume : Alpha 8
  priceX10000 : Alpha 8
  cmtaBroker : Alpha 4
  accountType : AccountType
  subtraderId : Alpha 3
  openClose : OpenClose
  executingBroker : Alpha 4
  clientAccountNumber : Alpha 12
  clientOrderId : Alpha 20
  clientMemo : Alpha 16
  liquidityStatus : LiquidityStatus
  tradeType : TradeType
  oppositeAccountType : OppositeAccountType
  participantSessionName : Alpha 12
  uniqueTransactionId : Alpha 10
  parentTransactionId : Alpha 10
  oppositeExecutingBroker : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace Allocation

def encode (message : Allocation) : List UInt8 :=
  Alpha.encode message.tradeNumber
    ++ (TransactionType.encode message.transactionType
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.priceX10000
    ++ (Alpha.encode message.cmtaBroker
    ++ (AccountType.encode message.accountType
    ++ (Alpha.encode message.subtraderId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clientMemo
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (TradeType.encode message.tradeType
    ++ (OppositeAccountType.encode message.oppositeAccountType
    ++ (Alpha.encode message.participantSessionName
    ++ (Alpha.encode message.uniqueTransactionId
    ++ (Alpha.encode message.parentTransactionId
    ++ (Alpha.encode message.oppositeExecutingBroker
    ++ (Alpha.encode message.additionalClientMemo)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (Allocation × List UInt8) := do
  let (tradeNumber, bytes) ← Alpha.decode 15 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (expirationDate, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← Alpha.decode 8 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceX10000, bytes) ← Alpha.decode 8 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (oppositeAccountType, bytes) ← OppositeAccountType.decode bytes
  let (participantSessionName, bytes) ← Alpha.decode 12 bytes
  let (uniqueTransactionId, bytes) ← Alpha.decode 10 bytes
  let (parentTransactionId, bytes) ← Alpha.decode 10 bytes
  let (oppositeExecutingBroker, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ tradeNumber, transactionType, timestamp, symbol, expirationDate, strikePrice, strikePriceFractionIndicator, optionType, volume, priceX10000, cmtaBroker, accountType, subtraderId, openClose, executingBroker, clientAccountNumber, clientOrderId, clientMemo, liquidityStatus, tradeType, oppositeAccountType, participantSessionName, uniqueTransactionId, parentTransactionId, oppositeExecutingBroker, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : Allocation) : (encode message).length = 200 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TransactionType.encode_length, OptionType.encode_length, AccountType.encode_length, OpenClose.encode_length, LiquidityStatus.encode_length, TradeType.encode_length, OppositeAccountType.encode_length]

theorem encode_length_pos (message : Allocation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : Allocation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeAccountType.decode_encode, some_bind]
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

end Allocation

/-- Allocation Cancel: 200 bytes -/
structure AllocationCancel where
  tradeNumber : Alpha 15
  transactionType : TransactionType
  timestamp : Alpha 6
  symbol : Alpha 30
  expirationDate : Alpha 6
  strikePrice : Alpha 8
  strikePriceFractionIndicator : Alpha 1
  optionType : OptionType
  volume : Alpha 8
  priceX10000 : Alpha 8
  cmtaBroker : Alpha 4
  accountType : AccountType
  subtraderId : Alpha 3
  openClose : OpenClose
  executingBroker : Alpha 4
  clientAccountNumber : Alpha 12
  clientOrderId : Alpha 20
  clientMemo : Alpha 16
  liquidityStatus : LiquidityStatus
  tradeType : TradeType
  oppositeAccountType : OppositeAccountType
  participantSessionName : Alpha 12
  uniqueTransactionId : Alpha 10
  parentTransactionId : Alpha 10
  oppositeExecutingBroker : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace AllocationCancel

def encode (message : AllocationCancel) : List UInt8 :=
  Alpha.encode message.tradeNumber
    ++ (TransactionType.encode message.transactionType
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.priceX10000
    ++ (Alpha.encode message.cmtaBroker
    ++ (AccountType.encode message.accountType
    ++ (Alpha.encode message.subtraderId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clientMemo
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (TradeType.encode message.tradeType
    ++ (OppositeAccountType.encode message.oppositeAccountType
    ++ (Alpha.encode message.participantSessionName
    ++ (Alpha.encode message.uniqueTransactionId
    ++ (Alpha.encode message.parentTransactionId
    ++ (Alpha.encode message.oppositeExecutingBroker
    ++ (Alpha.encode message.additionalClientMemo)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (AllocationCancel × List UInt8) := do
  let (tradeNumber, bytes) ← Alpha.decode 15 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (expirationDate, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← Alpha.decode 8 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceX10000, bytes) ← Alpha.decode 8 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (oppositeAccountType, bytes) ← OppositeAccountType.decode bytes
  let (participantSessionName, bytes) ← Alpha.decode 12 bytes
  let (uniqueTransactionId, bytes) ← Alpha.decode 10 bytes
  let (parentTransactionId, bytes) ← Alpha.decode 10 bytes
  let (oppositeExecutingBroker, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ tradeNumber, transactionType, timestamp, symbol, expirationDate, strikePrice, strikePriceFractionIndicator, optionType, volume, priceX10000, cmtaBroker, accountType, subtraderId, openClose, executingBroker, clientAccountNumber, clientOrderId, clientMemo, liquidityStatus, tradeType, oppositeAccountType, participantSessionName, uniqueTransactionId, parentTransactionId, oppositeExecutingBroker, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : AllocationCancel) : (encode message).length = 200 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TransactionType.encode_length, OptionType.encode_length, AccountType.encode_length, OpenClose.encode_length, LiquidityStatus.encode_length, TradeType.encode_length, OppositeAccountType.encode_length]

theorem encode_length_pos (message : AllocationCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : AllocationCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeAccountType.decode_encode, some_bind]
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

end AllocationCancel

/-- Give Up: 208 bytes -/
structure GiveUp where
  tradeNumber : Alpha 15
  transactionType : TransactionType
  timestamp : Alpha 6
  symbol : Alpha 30
  expirationDate : Alpha 6
  strikePrice : Alpha 8
  strikePriceFractionIndicator : Alpha 1
  optionType : OptionType
  volume : Alpha 8
  priceX10000 : Alpha 8
  cmtaBroker : Alpha 4
  accountType : AccountType
  subtraderId : Alpha 3
  openClose : OpenClose
  executingBroker : Alpha 4
  clientAccountNumber : Alpha 12
  clientOrderId : Alpha 20
  clientMemo : Alpha 16
  liquidityStatus : LiquidityStatus
  tradeType : TradeType
  oppositeAccountType : OppositeAccountType
  giveUpSource : Alpha 4
  giveUpDestination : Alpha 4
  participantSessionName : Alpha 12
  uniqueTransactionId : Alpha 10
  parentTransactionId : Alpha 10
  oppositeExecutingBroker : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace GiveUp

def encode (message : GiveUp) : List UInt8 :=
  Alpha.encode message.tradeNumber
    ++ (TransactionType.encode message.transactionType
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.priceX10000
    ++ (Alpha.encode message.cmtaBroker
    ++ (AccountType.encode message.accountType
    ++ (Alpha.encode message.subtraderId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clientMemo
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (TradeType.encode message.tradeType
    ++ (OppositeAccountType.encode message.oppositeAccountType
    ++ (Alpha.encode message.giveUpSource
    ++ (Alpha.encode message.giveUpDestination
    ++ (Alpha.encode message.participantSessionName
    ++ (Alpha.encode message.uniqueTransactionId
    ++ (Alpha.encode message.parentTransactionId
    ++ (Alpha.encode message.oppositeExecutingBroker
    ++ (Alpha.encode message.additionalClientMemo)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (GiveUp × List UInt8) := do
  let (tradeNumber, bytes) ← Alpha.decode 15 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (expirationDate, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← Alpha.decode 8 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceX10000, bytes) ← Alpha.decode 8 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (oppositeAccountType, bytes) ← OppositeAccountType.decode bytes
  let (giveUpSource, bytes) ← Alpha.decode 4 bytes
  let (giveUpDestination, bytes) ← Alpha.decode 4 bytes
  let (participantSessionName, bytes) ← Alpha.decode 12 bytes
  let (uniqueTransactionId, bytes) ← Alpha.decode 10 bytes
  let (parentTransactionId, bytes) ← Alpha.decode 10 bytes
  let (oppositeExecutingBroker, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ tradeNumber, transactionType, timestamp, symbol, expirationDate, strikePrice, strikePriceFractionIndicator, optionType, volume, priceX10000, cmtaBroker, accountType, subtraderId, openClose, executingBroker, clientAccountNumber, clientOrderId, clientMemo, liquidityStatus, tradeType, oppositeAccountType, giveUpSource, giveUpDestination, participantSessionName, uniqueTransactionId, parentTransactionId, oppositeExecutingBroker, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : GiveUp) : (encode message).length = 208 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TransactionType.encode_length, OptionType.encode_length, AccountType.encode_length, OpenClose.encode_length, LiquidityStatus.encode_length, TradeType.encode_length, OppositeAccountType.encode_length]

theorem encode_length_pos (message : GiveUp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : GiveUp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeAccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end GiveUp

/-- Give Up Cancel: 208 bytes -/
structure GiveUpCancel where
  tradeNumber : Alpha 15
  transactionType : TransactionType
  timestamp : Alpha 6
  symbol : Alpha 30
  expirationDate : Alpha 6
  strikePrice : Alpha 8
  strikePriceFractionIndicator : Alpha 1
  optionType : OptionType
  volume : Alpha 8
  priceX10000 : Alpha 8
  cmtaBroker : Alpha 4
  accountType : AccountType
  subtraderId : Alpha 3
  openClose : OpenClose
  executingBroker : Alpha 4
  clientAccountNumber : Alpha 12
  clientOrderId : Alpha 20
  clientMemo : Alpha 16
  liquidityStatus : LiquidityStatus
  tradeType : TradeType
  oppositeAccountType : OppositeAccountType
  giveUpSource : Alpha 4
  giveUpDestination : Alpha 4
  participantSessionName : Alpha 12
  uniqueTransactionId : Alpha 10
  parentTransactionId : Alpha 10
  oppositeExecutingBroker : Alpha 4
  additionalClientMemo : Alpha 16
  deriving DecidableEq, Repr

namespace GiveUpCancel

def encode (message : GiveUpCancel) : List UInt8 :=
  Alpha.encode message.tradeNumber
    ++ (TransactionType.encode message.transactionType
    ++ (Alpha.encode message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceFractionIndicator
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.priceX10000
    ++ (Alpha.encode message.cmtaBroker
    ++ (AccountType.encode message.accountType
    ++ (Alpha.encode message.subtraderId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.executingBroker
    ++ (Alpha.encode message.clientAccountNumber
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clientMemo
    ++ (LiquidityStatus.encode message.liquidityStatus
    ++ (TradeType.encode message.tradeType
    ++ (OppositeAccountType.encode message.oppositeAccountType
    ++ (Alpha.encode message.giveUpSource
    ++ (Alpha.encode message.giveUpDestination
    ++ (Alpha.encode message.participantSessionName
    ++ (Alpha.encode message.uniqueTransactionId
    ++ (Alpha.encode message.parentTransactionId
    ++ (Alpha.encode message.oppositeExecutingBroker
    ++ (Alpha.encode message.additionalClientMemo)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (GiveUpCancel × List UInt8) := do
  let (tradeNumber, bytes) ← Alpha.decode 15 bytes
  let (transactionType, bytes) ← TransactionType.decode bytes
  let (timestamp, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (expirationDate, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← Alpha.decode 8 bytes
  let (strikePriceFractionIndicator, bytes) ← Alpha.decode 1 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceX10000, bytes) ← Alpha.decode 8 bytes
  let (cmtaBroker, bytes) ← Alpha.decode 4 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (subtraderId, bytes) ← Alpha.decode 3 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (executingBroker, bytes) ← Alpha.decode 4 bytes
  let (clientAccountNumber, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clientMemo, bytes) ← Alpha.decode 16 bytes
  let (liquidityStatus, bytes) ← LiquidityStatus.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (oppositeAccountType, bytes) ← OppositeAccountType.decode bytes
  let (giveUpSource, bytes) ← Alpha.decode 4 bytes
  let (giveUpDestination, bytes) ← Alpha.decode 4 bytes
  let (participantSessionName, bytes) ← Alpha.decode 12 bytes
  let (uniqueTransactionId, bytes) ← Alpha.decode 10 bytes
  let (parentTransactionId, bytes) ← Alpha.decode 10 bytes
  let (oppositeExecutingBroker, bytes) ← Alpha.decode 4 bytes
  let (additionalClientMemo, bytes) ← Alpha.decode 16 bytes
  pure ({ tradeNumber, transactionType, timestamp, symbol, expirationDate, strikePrice, strikePriceFractionIndicator, optionType, volume, priceX10000, cmtaBroker, accountType, subtraderId, openClose, executingBroker, clientAccountNumber, clientOrderId, clientMemo, liquidityStatus, tradeType, oppositeAccountType, giveUpSource, giveUpDestination, participantSessionName, uniqueTransactionId, parentTransactionId, oppositeExecutingBroker, additionalClientMemo }, bytes)

@[simp] theorem encode_length (message : GiveUpCancel) : (encode message).length = 208 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TransactionType.encode_length, OptionType.encode_length, AccountType.encode_length, OpenClose.encode_length, LiquidityStatus.encode_length, TradeType.encode_length, OppositeAccountType.encode_length]

theorem encode_length_pos (message : GiveUpCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : GiveUpCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OppositeAccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end GiveUpCancel

/-- Acknowledgement Message: 0 bytes -/
structure AcknowledgementMessage where
  deriving DecidableEq, Repr

namespace AcknowledgementMessage

def encode (_ : AcknowledgementMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AcknowledgementMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AcknowledgementMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AcknowledgementMessage

/-- Error Message: 86 bytes -/
structure ErrorMessage where
  referenceMessageType : Alpha 2
  errorCode : Alpha 4
  errorText : Alpha 80
  deriving DecidableEq, Repr

namespace ErrorMessage

def encode (message : ErrorMessage) : List UInt8 :=
  Alpha.encode message.referenceMessageType
    ++ (Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorText))

def decode (bytes : List UInt8) : Option (ErrorMessage × List UInt8) := do
  let (referenceMessageType, bytes) ← Alpha.decode 2 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorText, bytes) ← Alpha.decode 80 bytes
  pure ({ referenceMessageType, errorCode, errorText }, bytes)

@[simp] theorem encode_length (message : ErrorMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorMessage

/-- Any Server Message, selected by Message Type -/
inductive ServerMessage where
  | startOfDay (message : StartOfDay) -- "00" 0x3030
  | circuitAssurance (message : CircuitAssurance) -- "02" 0x3032
  | restartAccepted (message : RestartAccepted) -- "05" 0x3035
  | endOfTrading (message : EndOfTrading) -- "08" 0x3038
  | clientSignonAcknowledgment (message : ClientSignonAcknowledgment) -- "10" 0x3130
  | trade (message : Trade) -- "30" 0x3330
  | tradeCancel (message : TradeCancel) -- "31" 0x3331
  | allocation (message : Allocation) -- "40" 0x3430
  | allocationCancel (message : AllocationCancel) -- "41" 0x3431
  | giveUp (message : GiveUp) -- "50" 0x3530
  | giveUpCancel (message : GiveUpCancel) -- "51" 0x3531
  | acknowledgementMessage (message : AcknowledgementMessage) -- "98" 0x3938
  | errorMessage (message : ErrorMessage) -- "99" 0x3939
  deriving DecidableEq, Repr

namespace ServerMessage

/-- The Message Type each message is sent under -/
def tag : ServerMessage → BitVec 16
  | .startOfDay _ => 12336
  | .circuitAssurance _ => 12338
  | .restartAccepted _ => 12341
  | .endOfTrading _ => 12344
  | .clientSignonAcknowledgment _ => 12592
  | .trade _ => 13104
  | .tradeCancel _ => 13105
  | .allocation _ => 13360
  | .allocationCancel _ => 13361
  | .giveUp _ => 13616
  | .giveUpCancel _ => 13617
  | .acknowledgementMessage _ => 14648
  | .errorMessage _ => 14649

def encode : ServerMessage → List UInt8
  | .startOfDay message => StartOfDay.encode message
  | .circuitAssurance message => CircuitAssurance.encode message
  | .restartAccepted message => RestartAccepted.encode message
  | .endOfTrading message => EndOfTrading.encode message
  | .clientSignonAcknowledgment message => ClientSignonAcknowledgment.encode message
  | .trade message => Trade.encode message
  | .tradeCancel message => TradeCancel.encode message
  | .allocation message => Allocation.encode message
  | .allocationCancel message => AllocationCancel.encode message
  | .giveUp message => GiveUp.encode message
  | .giveUpCancel message => GiveUpCancel.encode message
  | .acknowledgementMessage message => AcknowledgementMessage.encode message
  | .errorMessage message => ErrorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerMessage) : (encode message).length ≤ 208 := by
  cases message with
  | startOfDay inner =>
    simp only [encode, StartOfDay.encode_length]
    omega
  | circuitAssurance inner =>
    simp only [encode, CircuitAssurance.encode_length]
    omega
  | restartAccepted inner =>
    simp only [encode, RestartAccepted.encode_length]
    omega
  | endOfTrading inner =>
    simp only [encode, EndOfTrading.encode_length]
    omega
  | clientSignonAcknowledgment inner =>
    simp only [encode, ClientSignonAcknowledgment.encode_length]
    omega
  | trade inner =>
    simp only [encode, Trade.encode_length]
    omega
  | tradeCancel inner =>
    simp only [encode, TradeCancel.encode_length]
    omega
  | allocation inner =>
    simp only [encode, Allocation.encode_length]
    omega
  | allocationCancel inner =>
    simp only [encode, AllocationCancel.encode_length]
    omega
  | giveUp inner =>
    simp only [encode, GiveUp.encode_length]
    omega
  | giveUpCancel inner =>
    simp only [encode, GiveUpCancel.encode_length]
    omega
  | acknowledgementMessage inner =>
    simp only [encode, AcknowledgementMessage.encode_length]
    omega
  | errorMessage inner =>
    simp only [encode, ErrorMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessage × List UInt8) :=
  if tag = 12336 then (StartOfDay.decode bytes).map fun (message, rest) => (.startOfDay message, rest)
  else if tag = 12338 then (CircuitAssurance.decode bytes).map fun (message, rest) => (.circuitAssurance message, rest)
  else if tag = 12341 then (RestartAccepted.decode bytes).map fun (message, rest) => (.restartAccepted message, rest)
  else if tag = 12344 then (EndOfTrading.decode bytes).map fun (message, rest) => (.endOfTrading message, rest)
  else if tag = 12592 then (ClientSignonAcknowledgment.decode bytes).map fun (message, rest) => (.clientSignonAcknowledgment message, rest)
  else if tag = 13104 then (Trade.decode bytes).map fun (message, rest) => (.trade message, rest)
  else if tag = 13105 then (TradeCancel.decode bytes).map fun (message, rest) => (.tradeCancel message, rest)
  else if tag = 13360 then (Allocation.decode bytes).map fun (message, rest) => (.allocation message, rest)
  else if tag = 13361 then (AllocationCancel.decode bytes).map fun (message, rest) => (.allocationCancel message, rest)
  else if tag = 13616 then (GiveUp.decode bytes).map fun (message, rest) => (.giveUp message, rest)
  else if tag = 13617 then (GiveUpCancel.decode bytes).map fun (message, rest) => (.giveUpCancel message, rest)
  else if tag = 14648 then (AcknowledgementMessage.decode bytes).map fun (message, rest) => (.acknowledgementMessage message, rest)
  else if tag = 14649 then (ErrorMessage.decode bytes).map fun (message, rest) => (.errorMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerMessage

/-- Server Packet -/
structure ServerPacket where
  source : Alpha 4
  destination : Alpha 4
  messageFlag : MessageFlag
  controlByte : Alpha 1
  sequenceNumber : Alpha 8
  acknowledgementSequenceNumber : Alpha 8
  serverMessage : ServerMessage
  endOfText : BitVec 8
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  Alpha.encode message.source
    ++ (Alpha.encode message.destination
    ++ (encodeUInt 2 (ServerMessage.tag message.serverMessage)
    ++ (MessageFlag.encode message.messageFlag
    ++ (Alpha.encode message.controlByte
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.acknowledgementSequenceNumber
    ++ (ServerMessage.encode message.serverMessage
    ++ (encodeUInt 1 message.endOfText))))))))

def decode (bytes : List UInt8) : Option (ServerPacket × List UInt8) := do
  let (source, bytes) ← Alpha.decode 4 bytes
  let (destination, bytes) ← Alpha.decode 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageFlag, bytes) ← MessageFlag.decode bytes
  let (controlByte, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (acknowledgementSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (serverMessage, bytes) ← ServerMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  pure ({ source, destination, messageFlag, controlByte, sequenceNumber, acknowledgementSequenceNumber, serverMessage, endOfText }, bytes)

theorem encode_length_pos (message : ServerPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerPacket) : (encode message).length ≤ 237 := by
  unfold encode
  cases message.serverMessage with
  | startOfDay inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, StartOfDay.encode_length]
    omega
  | circuitAssurance inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, CircuitAssurance.encode_length]
    omega
  | restartAccepted inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, RestartAccepted.encode_length]
    omega
  | endOfTrading inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, EndOfTrading.encode_length]
    omega
  | clientSignonAcknowledgment inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, ClientSignonAcknowledgment.encode_length]
    omega
  | trade inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, Trade.encode_length]
    omega
  | tradeCancel inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, TradeCancel.encode_length]
    omega
  | allocation inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, Allocation.encode_length]
    omega
  | allocationCancel inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, AllocationCancel.encode_length]
    omega
  | giveUp inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, GiveUp.encode_length]
    omega
  | giveUpCancel inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, GiveUpCancel.encode_length]
    omega
  | acknowledgementMessage inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, AcknowledgementMessage.encode_length]
    omega
  | errorMessage inner =>
    simp only [ServerMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageFlag.encode_length, ErrorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ServerPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ServerMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ServerPacket

end Omi.BoxBoxoptionsSolatradereportingAtrV45Server
