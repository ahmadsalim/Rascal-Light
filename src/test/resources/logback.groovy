appender("TEST-FILE", FileAppender) {
    file = "./log/absint-rascal-test.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("FILE", FileAppender) {
    file = "./log/absint-rascal.log"
    append = true
    encoder(PatternLayoutEncoder) {
        pattern = "%level %logger - %msg%n"
    }
}

logger("test", ALL, ["TEST-FILE"], false)
logger("evaluation", ALL, ["EVALUATION-FILE"], false)
root(DEBUG, ["FILE"])