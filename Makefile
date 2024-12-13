APA_VERSION=0.47.0
APA_RELEASE_URL=https://github.com/apalache-mc/apalache/releases/download/v${APA_VERSION}/apalache-${APA_VERSION}.tgz
APA=apalache-${APA_VERSION}
APA_ARCHIVE=$(APA).tgz
TLA_TOOLS_JAR=tla2tools.jar
TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
TLC_WORKERS=2
TLC_OFFHEAP_MEMORY=3G
TLC_HEAP=1G

all:

$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

$(TLA_TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TLA_TOOLS_JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(APA) $(TLA_TOOLS_JAR)

verify: $(APA)
	APA=$(APA) ./check.sh -inductive TypeOK Termination
	APA=$(APA) ./check.sh -relative Safety_ Safety Termination

%.pdf: %.tla $(TLA_TOOLS_JAR)
	java -cp $(TLA_TOOLS_JAR) tla2tex.TLA -shade -ps -latexCommand pdflatex $<

PDF_FILES := Termination.pdf TerminationPlusCal.pdf

typeset: $(PDF_FILES)

transpile: TerminationPlusCal.tla
	java -cp $(TLA_TOOLS_JAR) pcal.trans -nocfg $<

tlc: Termination.tla $(TLA_TOOLS_JAR)
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} Termination.tla

pluscal-tlc: Termination.tla $(TLA_TOOLS_JAR) transpile
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} TerminationPlusCal.tla

.PHONY: all typeset verify transpile

