import Wire

/-!
# Nextrade Nextrade Stock Market Data 3 Level v2.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NextradeNextradeStock3levelNxtasciiV212

/-- Polling Data Message: 5 bytes -/
structure PollingDataMessage where
  currentTime1MinuteInterval : Alpha 4
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace PollingDataMessage

def encode (message : PollingDataMessage) : List UInt8 :=
  Alpha.encode message.currentTime1MinuteInterval
    ++ (Alpha.encode message.endKeyword)

def decode (bytes : List UInt8) : Option (PollingDataMessage × List UInt8) := do
  let (currentTime1MinuteInterval, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ currentTime1MinuteInterval, endKeyword }, bytes)

@[simp] theorem encode_length (message : PollingDataMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : PollingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PollingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PollingDataMessage

/-- Securities Quote 3 Level Message: 263 bytes -/
structure SecuritiesQuote3LevelMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  totalAskVolumeLevel10 : Alpha 12
  totalBidVolumeLevel10 : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesQuote3LevelMessage

def encode (message : SecuritiesQuote3LevelMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.totalAskVolumeLevel10
    ++ (Alpha.encode message.totalBidVolumeLevel10
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesQuote3LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolumeLevel10, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolumeLevel10, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, totalAskVolumeLevel10, totalBidVolumeLevel10, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesQuote3LevelMessage) : (encode message).length = 263 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesQuote3LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesQuote3LevelMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecuritiesQuote3LevelMessage

/-- Securities Order Filled Plus Quote 3 Level Message: 356 bytes -/
structure SecuritiesOrderFilledPlusQuote3LevelMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  tradingPrice : Alpha 11
  tradingVolume : Alpha 10
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : Alpha 15
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  totalAskVolumeLevel10 : Alpha 12
  totalBidVolumeLevel10 : Alpha 12
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledPlusQuote3LevelMessage

def encode (message : SecuritiesOrderFilledPlusQuote3LevelMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (Alpha.encode message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.lpHoldingQuantity
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.totalAskVolumeLevel10
    ++ (Alpha.encode message.totalBidVolumeLevel10
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledPlusQuote3LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (tradingPrice, bytes) ← Alpha.decode 11 bytes
  let (tradingVolume, bytes) ← Alpha.decode 10 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← Alpha.decode 15 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolumeLevel10, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolumeLevel10, bytes) ← Alpha.decode 12 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, totalAskVolumeLevel10, totalBidVolumeLevel10, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledPlusQuote3LevelMessage) : (encode message).length = 356 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledPlusQuote3LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesOrderFilledPlusQuote3LevelMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecuritiesOrderFilledPlusQuote3LevelMessage

/-- Market Operation Ts Plus Quote 3 Level Message: 283 bytes -/
structure MarketOperationTsPlusQuote3LevelMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  tradingHaltReasonCode : Alpha 3
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  totalAskVolumeLevel10 : Alpha 12
  totalBidVolumeLevel10 : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationTsPlusQuote3LevelMessage

def encode (message : MarketOperationTsPlusQuote3LevelMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.totalAskVolumeLevel10
    ++ (Alpha.encode message.totalBidVolumeLevel10
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MarketOperationTsPlusQuote3LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolumeLevel10, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolumeLevel10, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, totalAskVolumeLevel10, totalBidVolumeLevel10, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsPlusQuote3LevelMessage) : (encode message).length = 283 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsPlusQuote3LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MarketOperationTsPlusQuote3LevelMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketOperationTsPlusQuote3LevelMessage

/-- Securities Order Filled Message: 181 bytes -/
structure SecuritiesOrderFilledMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  tradingPrice : Alpha 11
  tradingVolume : Alpha 10
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : Alpha 15
  theBestAsk : Alpha 11
  theBestBid : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledMessage

def encode (message : SecuritiesOrderFilledMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (Alpha.encode message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.lpHoldingQuantity
    ++ (Alpha.encode message.theBestAsk
    ++ (Alpha.encode message.theBestBid
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (tradingPrice, bytes) ← Alpha.decode 11 bytes
  let (tradingVolume, bytes) ← Alpha.decode 10 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← Alpha.decode 15 bytes
  let (theBestAsk, bytes) ← Alpha.decode 11 bytes
  let (theBestBid, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, theBestAsk, theBestBid, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledMessage) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesOrderFilledMessage) (rest : List UInt8) :
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

end SecuritiesOrderFilledMessage

/-- Market Operation Ts Message: 63 bytes -/
structure MarketOperationTsMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  tradingHaltReasonCode : Alpha 3
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationTsMessage

def encode (message : MarketOperationTsMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationTsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationTsMessage) (rest : List UInt8) :
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

end MarketOperationTsMessage

/-- Issue Closing Message: 107 bytes -/
structure IssueClosingMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  closingPrice : Alpha 11
  closingPriceTypeCode : Alpha 1
  upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  closingPriceWeightedStockPriceAverage : Alpha 11
  closingPriceBasePriceOfBuyIn : Alpha 11
  closingPriceUpperLimitOfBuyIn : Alpha 11
  closingPriceLowerLimitOfBuyIn : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace IssueClosingMessage

def encode (message : IssueClosingMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.closingPriceWeightedStockPriceAverage
    ++ (Alpha.encode message.closingPriceBasePriceOfBuyIn
    ++ (Alpha.encode message.closingPriceUpperLimitOfBuyIn
    ++ (Alpha.encode message.closingPriceLowerLimitOfBuyIn
    ++ (Alpha.encode message.endKeyword))))))))))))

def decode (bytes : List UInt8) : Option (IssueClosingMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (closingPrice, bytes) ← Alpha.decode 11 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (closingPriceWeightedStockPriceAverage, bytes) ← Alpha.decode 11 bytes
  let (closingPriceBasePriceOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceUpperLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceLowerLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, closingPrice, closingPriceTypeCode, upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, closingPriceWeightedStockPriceAverage, closingPriceBasePriceOfBuyIn, closingPriceUpperLimitOfBuyIn, closingPriceLowerLimitOfBuyIn, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueClosingMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IssueClosingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueClosingMessage) (rest : List UInt8) :
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

end IssueClosingMessage

/-- Triggering Removing Vi Message: 111 bytes -/
structure TriggeringRemovingViMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  theTimeEndingVi : Alpha 9
  viStatusCode : Alpha 1
  viTypeCode : Alpha 1
  aBasePriceToTriggerStaticVi : Alpha 11
  aBasePriceToTriggerDynamicVi : Alpha 11
  viTriggeringPrice : Alpha 11
  disparateRatioToTriggerStaticVi : Alpha 13
  disparateRatioToTriggerDynamicVi : Alpha 13
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TriggeringRemovingViMessage

def encode (message : TriggeringRemovingViMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.theTimeEndingVi
    ++ (Alpha.encode message.viStatusCode
    ++ (Alpha.encode message.viTypeCode
    ++ (Alpha.encode message.aBasePriceToTriggerStaticVi
    ++ (Alpha.encode message.aBasePriceToTriggerDynamicVi
    ++ (Alpha.encode message.viTriggeringPrice
    ++ (Alpha.encode message.disparateRatioToTriggerStaticVi
    ++ (Alpha.encode message.disparateRatioToTriggerDynamicVi
    ++ (Alpha.encode message.endKeyword)))))))))))))

def decode (bytes : List UInt8) : Option (TriggeringRemovingViMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (theTimeEndingVi, bytes) ← Alpha.decode 9 bytes
  let (viStatusCode, bytes) ← Alpha.decode 1 bytes
  let (viTypeCode, bytes) ← Alpha.decode 1 bytes
  let (aBasePriceToTriggerStaticVi, bytes) ← Alpha.decode 11 bytes
  let (aBasePriceToTriggerDynamicVi, bytes) ← Alpha.decode 11 bytes
  let (viTriggeringPrice, bytes) ← Alpha.decode 11 bytes
  let (disparateRatioToTriggerStaticVi, bytes) ← Alpha.decode 13 bytes
  let (disparateRatioToTriggerDynamicVi, bytes) ← Alpha.decode 13 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, theTimeEndingVi, viStatusCode, viTypeCode, aBasePriceToTriggerStaticVi, aBasePriceToTriggerDynamicVi, viTriggeringPrice, disparateRatioToTriggerStaticVi, disparateRatioToTriggerDynamicVi, endKeyword }, bytes)

@[simp] theorem encode_length (message : TriggeringRemovingViMessage) : (encode message).length = 111 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TriggeringRemovingViMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TriggeringRemovingViMessage) (rest : List UInt8) :
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

end TriggeringRemovingViMessage

/-- Closing Price Trading Quote Message: 53 bytes -/
structure ClosingPriceTradingQuoteMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ClosingPriceTradingQuoteMessage

def encode (message : ClosingPriceTradingQuoteMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (ClosingPriceTradingQuoteMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, totalAskVolume, totalBidVolume, endKeyword }, bytes)

@[simp] theorem encode_length (message : ClosingPriceTradingQuoteMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceTradingQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceTradingQuoteMessage) (rest : List UInt8) :
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

end ClosingPriceTradingQuoteMessage

/-- Any Payload, selected by TR Code -/
inductive Payload where
  | pollingDataMessage (message : PollingDataMessage) -- "I2500" 0x4932353030
  | securitiesQuote3LevelMessage (message : SecuritiesQuote3LevelMessage) -- "B651S" 0x4236353153
  | securitiesQuote3LevelMessage284377297233 (message : SecuritiesQuote3LevelMessage) -- "B651Q" 0x4236353151
  | securitiesOrderFilledPlusQuote3LevelMessage (message : SecuritiesOrderFilledPlusQuote3LevelMessage) -- "G751S" 0x4737353153
  | securitiesOrderFilledPlusQuote3LevelMessage305868910929 (message : SecuritiesOrderFilledPlusQuote3LevelMessage) -- "G751Q" 0x4737353151
  | marketOperationTsPlusQuote3LevelMessage (message : MarketOperationTsPlusQuote3LevelMessage) -- "R151S" 0x5231353153
  | marketOperationTsPlusQuote3LevelMessage353012887889 (message : MarketOperationTsPlusQuote3LevelMessage) -- "R151Q" 0x5231353151
  | securitiesOrderFilledMessage (message : SecuritiesOrderFilledMessage) -- "A351S" 0x4133353153
  | securitiesOrderFilledMessage280031998289 (message : SecuritiesOrderFilledMessage) -- "A351Q" 0x4133353151
  | marketOperationTsMessage (message : MarketOperationTsMessage) -- "A751S" 0x4137353153
  | marketOperationTsMessage280099107153 (message : MarketOperationTsMessage) -- "A751Q" 0x4137353151
  | issueClosingMessage (message : IssueClosingMessage) -- "A651S" 0x4136353153
  | issueClosingMessage280082329937 (message : IssueClosingMessage) -- "A651Q" 0x4136353151
  | triggeringRemovingViMessage (message : TriggeringRemovingViMessage) -- "R851S" 0x5238353153
  | triggeringRemovingViMessage353130328401 (message : TriggeringRemovingViMessage) -- "R851Q" 0x5238353151
  | closingPriceTradingQuoteMessage (message : ClosingPriceTradingQuoteMessage) -- "E151S" 0x4531353153
  | closingPriceTradingQuoteMessage297178313041 (message : ClosingPriceTradingQuoteMessage) -- "E151Q" 0x4531353151
  deriving DecidableEq, Repr

namespace Payload

/-- The TR Code each message is sent under -/
def tag : Payload → BitVec 40
  | .pollingDataMessage _ => 314374959152
  | .securitiesQuote3LevelMessage _ => 284377297235
  | .securitiesQuote3LevelMessage284377297233 _ => 284377297233
  | .securitiesOrderFilledPlusQuote3LevelMessage _ => 305868910931
  | .securitiesOrderFilledPlusQuote3LevelMessage305868910929 _ => 305868910929
  | .marketOperationTsPlusQuote3LevelMessage _ => 353012887891
  | .marketOperationTsPlusQuote3LevelMessage353012887889 _ => 353012887889
  | .securitiesOrderFilledMessage _ => 280031998291
  | .securitiesOrderFilledMessage280031998289 _ => 280031998289
  | .marketOperationTsMessage _ => 280099107155
  | .marketOperationTsMessage280099107153 _ => 280099107153
  | .issueClosingMessage _ => 280082329939
  | .issueClosingMessage280082329937 _ => 280082329937
  | .triggeringRemovingViMessage _ => 353130328403
  | .triggeringRemovingViMessage353130328401 _ => 353130328401
  | .closingPriceTradingQuoteMessage _ => 297178313043
  | .closingPriceTradingQuoteMessage297178313041 _ => 297178313041

def encode : Payload → List UInt8
  | .pollingDataMessage message => PollingDataMessage.encode message
  | .securitiesQuote3LevelMessage message => SecuritiesQuote3LevelMessage.encode message
  | .securitiesQuote3LevelMessage284377297233 message => SecuritiesQuote3LevelMessage.encode message
  | .securitiesOrderFilledPlusQuote3LevelMessage message => SecuritiesOrderFilledPlusQuote3LevelMessage.encode message
  | .securitiesOrderFilledPlusQuote3LevelMessage305868910929 message => SecuritiesOrderFilledPlusQuote3LevelMessage.encode message
  | .marketOperationTsPlusQuote3LevelMessage message => MarketOperationTsPlusQuote3LevelMessage.encode message
  | .marketOperationTsPlusQuote3LevelMessage353012887889 message => MarketOperationTsPlusQuote3LevelMessage.encode message
  | .securitiesOrderFilledMessage message => SecuritiesOrderFilledMessage.encode message
  | .securitiesOrderFilledMessage280031998289 message => SecuritiesOrderFilledMessage.encode message
  | .marketOperationTsMessage message => MarketOperationTsMessage.encode message
  | .marketOperationTsMessage280099107153 message => MarketOperationTsMessage.encode message
  | .issueClosingMessage message => IssueClosingMessage.encode message
  | .issueClosingMessage280082329937 message => IssueClosingMessage.encode message
  | .triggeringRemovingViMessage message => TriggeringRemovingViMessage.encode message
  | .triggeringRemovingViMessage353130328401 message => TriggeringRemovingViMessage.encode message
  | .closingPriceTradingQuoteMessage message => ClosingPriceTradingQuoteMessage.encode message
  | .closingPriceTradingQuoteMessage297178313041 message => ClosingPriceTradingQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 356 := by
  cases message with
  | pollingDataMessage inner =>
    simp only [encode, PollingDataMessage.encode_length]
    omega
  | securitiesQuote3LevelMessage inner =>
    simp only [encode, SecuritiesQuote3LevelMessage.encode_length]
    omega
  | securitiesQuote3LevelMessage284377297233 inner =>
    simp only [encode, SecuritiesQuote3LevelMessage.encode_length]
    omega
  | securitiesOrderFilledPlusQuote3LevelMessage inner =>
    simp only [encode, SecuritiesOrderFilledPlusQuote3LevelMessage.encode_length]
    omega
  | securitiesOrderFilledPlusQuote3LevelMessage305868910929 inner =>
    simp only [encode, SecuritiesOrderFilledPlusQuote3LevelMessage.encode_length]
    omega
  | marketOperationTsPlusQuote3LevelMessage inner =>
    simp only [encode, MarketOperationTsPlusQuote3LevelMessage.encode_length]
    omega
  | marketOperationTsPlusQuote3LevelMessage353012887889 inner =>
    simp only [encode, MarketOperationTsPlusQuote3LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | securitiesOrderFilledMessage280031998289 inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | marketOperationTsMessage280099107153 inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | issueClosingMessage280082329937 inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | triggeringRemovingViMessage353130328401 inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage297178313041 inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 314374959152 then (PollingDataMessage.decode bytes).map fun (message, rest) => (.pollingDataMessage message, rest)
  else if tag = 284377297235 then (SecuritiesQuote3LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuote3LevelMessage message, rest)
  else if tag = 284377297233 then (SecuritiesQuote3LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuote3LevelMessage284377297233 message, rest)
  else if tag = 305868910931 then (SecuritiesOrderFilledPlusQuote3LevelMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledPlusQuote3LevelMessage message, rest)
  else if tag = 305868910929 then (SecuritiesOrderFilledPlusQuote3LevelMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledPlusQuote3LevelMessage305868910929 message, rest)
  else if tag = 353012887891 then (MarketOperationTsPlusQuote3LevelMessage.decode bytes).map fun (message, rest) => (.marketOperationTsPlusQuote3LevelMessage message, rest)
  else if tag = 353012887889 then (MarketOperationTsPlusQuote3LevelMessage.decode bytes).map fun (message, rest) => (.marketOperationTsPlusQuote3LevelMessage353012887889 message, rest)
  else if tag = 280031998291 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage message, rest)
  else if tag = 280031998289 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage280031998289 message, rest)
  else if tag = 280099107155 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage message, rest)
  else if tag = 280099107153 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage280099107153 message, rest)
  else if tag = 280082329939 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage message, rest)
  else if tag = 280082329937 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage280082329937 message, rest)
  else if tag = 353130328403 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage message, rest)
  else if tag = 353130328401 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage353130328401 message, rest)
  else if tag = 297178313043 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage message, rest)
  else if tag = 297178313041 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage297178313041 message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 5 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (trCode, bytes) ← decodeUInt 5 bytes
  let (payload, bytes) ← Payload.decode trCode bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 361 := by
  unfold encode
  cases message.payload with
  | pollingDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PollingDataMessage.encode_length]
    omega
  | securitiesQuote3LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuote3LevelMessage.encode_length]
    omega
  | securitiesQuote3LevelMessage284377297233 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuote3LevelMessage.encode_length]
    omega
  | securitiesOrderFilledPlusQuote3LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledPlusQuote3LevelMessage.encode_length]
    omega
  | securitiesOrderFilledPlusQuote3LevelMessage305868910929 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledPlusQuote3LevelMessage.encode_length]
    omega
  | marketOperationTsPlusQuote3LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsPlusQuote3LevelMessage.encode_length]
    omega
  | marketOperationTsPlusQuote3LevelMessage353012887889 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsPlusQuote3LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | securitiesOrderFilledMessage280031998289 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | marketOperationTsMessage280099107153 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | issueClosingMessage280082329937 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | triggeringRemovingViMessage353130328401 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage297178313041 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NextradeNextradeStock3levelNxtasciiV212
