# This was taken and modified from 6.826 Labs (Fall 2020)

COQARGS		:= -w -undo-batch-mode
ALL_VFILES	:= $(sort $(shell find . -name "*.v"))
ALL_VOFILES	:= $(ALL_VFILES:.v=.vo)


default: $(ALL_VOFILES)


%.vo: %.v
	@echo "COQC $<"
	@coqc $(COQARGS) $< -o $@

clean:
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.vos) $(ALL_VFILES:.v=.vok) $(ALL_VFILES:.v=.glob)
	@find . -name ".*.aux" -exec rm {} \;