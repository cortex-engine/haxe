package runci.targets;

import sys.FileSystem;
import runci.System.*;
import runci.Config.*;

class Fiberus {
	static public var gotFiberusDependencies = false;
	static final miscFiberusDir = getMiscSubDir('fiberus');

	static public function getFiberusDependencies() {
		if (gotFiberusDependencies) return;

		// fiberus dependencies
		switch (systemName) {
			case "Linux":
				Linux.requireAptPackages(["gcc", "make"]);
			case "Mac":
				// pass
		}

		// install and build fiberus
		try {
			final path = getHaxelibPath("fiberus");
			infoMsg('fiberus has already been installed in $path.');
		} catch(e:Dynamic) {
			haxelibInstallGit("mib", "fiberus", true);
			final oldDir = Sys.getCwd();
			changeDirectory(getHaxelibPath("fiberus") + "tools/fiberus/");
			runCommand("haxe", ["-D", "source-header=''", "compile.hxml"]);
			changeDirectory(oldDir);
		}

		gotFiberusDependencies = true;
	}

	static public function runFiberus(bin:String, ?args:Array<String>):Void {
		if (args == null) args = [];
		bin = FileSystem.fullPath(bin);
		runCommand(bin, args);
	}

	static public function run(args:Array<String>) {
		getFiberusDependencies();

		// Run unit tests
		runCommand("rm", ["-rf", "bin/fiberus"]);
		runCommand("haxe", ["compile-fiberus.hxml"].concat(args));
		runFiberus("bin/fiberus/Main");

		// Run sys tests
		changeDirectory(sysDir);
		runCommand("haxe", ["--each", "compile-fiberus.hxml"].concat(args));
		runSysTest(FileSystem.fullPath("bin/fiberus/Main"));

		// Run threading tests (critical for fiber runtime)
		changeDirectory(threadsDir);
		runCommand("haxe", ["build.hxml", "--fiberus", "export/fiberus"]);
		runFiberus("export/fiberus/Main");

		// Run misc fiberus tests if they exist
		if (FileSystem.exists(miscFiberusDir)) {
			changeDirectory(miscFiberusDir);
			runCommand("haxe", ["run.hxml"]);
		}
	}
}
