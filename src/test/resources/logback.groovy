appender("TEST-FILE", FileAppender) {
    file = "./log/absint-rascal-test.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("NNF-EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-nnf-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("DESUGAR-OBERON-EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-desugar-oberon-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("GLAGOL-2-PHP-EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-glagol-2-php-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("MINI-CALC-EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-mini-calc-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("MINI-CONFIG-EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-mini-config-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("RENAME-FIELD-EVALUATION-FILE", FileAppender) {
    file = "./log/absint-rascal-rename-field-evaluation.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%msg%n"
    }
}

appender("FILE", FileAppender) {
    file = "./log/absint-rascal.log"
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%level %logger - %msg%n"
    }
}

logger("test", ALL, ["TEST-FILE"], false)
logger("nnf-evaluation", ALL, ["NNF-EVALUATION-FILE"], false)
logger("desugar-oberon-evaluation", ALL, ["DESUGAR-OBERON-EVALUATION-FILE"], false)
logger("glagol-2-php-evaluation", ALL, ["GLAGOL-2-PHP-EVALUATION-FILE"], false)
logger("mini-calc-evaluation", ALL, ["MINI-CALC-EVALUATION-FILE"], false)
logger("mini-config-evaluation", ALL, ["MINI-CONFIG-EVALUATION-FILE"], false)
logger("rename-field-evaluation", ALL, ["RENAME-FIELD-EVALUATION-FILE"], false)
root(DEBUG, ["FILE"])