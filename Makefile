TLA_JAR := tools/tla2tools.jar
JAVA := java -cp $(TLA_JAR)

TLC := $(JAVA) tlc2.TLC
PCAL := $(JAVA) pcal.trans

SPEC ?= beans

TLA := specs/$(SPEC).tla
CFG := specs/$(SPEC).cfg

BUILD := build
STATE_DIR := $(BUILD)/states/$(SPEC)
GRAPH_DIR := $(BUILD)/graphs

.PHONY: check translate graph clean

translate:
	$(PCAL) $(TLA)

check:
	mkdir -p $(STATE_DIR)
	$(TLC) \
		-workers auto \
		-checkpoint 0 \
		-metadir $(STATE_DIR) \
		$(TLA)

graph:
	mkdir -p $(GRAPH_DIR)
	$(TLC) \
		-deadlock \
		-dump dot $(GRAPH_DIR)/$(SPEC).dot \
		$(TLA)
	dot -Tpng $(GRAPH_DIR)/$(SPEC).dot -o $(GRAPH_DIR)/$(SPEC).png

clean:
	rm -rf build
