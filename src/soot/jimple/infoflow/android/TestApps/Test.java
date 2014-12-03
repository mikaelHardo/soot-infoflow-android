/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.android.TestApps;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.StringWriter;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import soot.jimple.infoflow.util.IntentTag;

import org.xmlpull.v1.XmlPullParserException;

import soot.SootMethod;
import soot.jimple.Stmt;
import soot.jimple.infoflow.IInfoflow.CallgraphAlgorithm;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.InfoflowResults;
import soot.jimple.infoflow.InfoflowResults.SinkInfo;
import soot.jimple.infoflow.InfoflowResults.SourceInfo;
import soot.jimple.infoflow.android.AndroidSourceSinkManager.LayoutMatchingMode;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory.PathBuilder;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.taintWrappers.TaintWrapperSet;
import soot.jimple.internal.AbstractInvokeExpr;

public class Test {
	
	private static final class MyResultsAvailableHandler implements
			ResultsAvailableHandler {
		private BufferedWriter wr;
		public String appPkgName;

		private MyResultsAvailableHandler() {
			this.wr = null;
		}

		private MyResultsAvailableHandler(BufferedWriter wr) {
			this.wr = wr;
		}
		
		// When flowdroid is finished
		@Override
		public void onResultsAvailable(
				IInfoflowCFG cfg, InfoflowResults results) {

			// Dump the results
			if (outFilename != null) {
				try {
					this.wr = new BufferedWriter(new FileWriter(outFilename));
				} catch (IOException ex) {
				}
			}
			
			if (results == null) {
				println("No results found.");
			
			} else {
				// Lets print the output as an XML file
				println("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
				println("<results package=\"" + escapeXML(this.appPkgName)
						+ "\">");
				
				// A flow can consist of multiple sources to one sink
				Set<SinkInfo> sinks = new TreeSet<SinkInfo>(results.getResults().keySet());

				for (SinkInfo sink : sinks) {
					// New flow
					println("<flow>");
					print("<sink method=\"" + escapeXML(getMethodSignature(sink.getContext())) + "\"");
					
					// If the sink is an "Intent Sink", we want to add more data to it. We get the Intent ID,
					// that are set by the app transformer, have already been retrieved and saved in a "Tag"
					if (Infoflow.isIntentSink(sink.getContext())) {
						print(" is-intent=\"1\"");
						print(" component-type=\"" + escapeXML(getComponentTypeFromMethod(sink.getContext())) + "\"");
						print(" intent-id=\"" + escapeXML(((IntentTag) sink.getContext().getTag("IntentID")).getIntentID()) + "\"");
					}
					// Again, if the sink is an IntentResult, we need some other data
					if (Infoflow.isIntentResultSink(sink.getContext())) {
						print(" is-intent-result=\"1\"");
						print(" component=\"" + escapeXML(cfg.getMethodOf(sink.getContext()).getDeclaringClass()) + "\"");
					}
					// sink ends
					println("></sink>");
					
					// The sources to one sink
					for (SourceInfo source : new TreeSet<SourceInfo>(results.getResults().get(sink))) {
						// We want to know the methodname of the source method
						println("<source method=\"" + escapeXML(getMethodSignature(source.getContext()))
								+ "\" component=\"" + escapeXML(cfg.getMethodOf(source.getContext()).getDeclaringClass()) + "\">");
						// We also want to know, what method the call happens in
						println("<in>" + escapeXML(cfg.getMethodOf(source.getContext()).getName()) + "</in>");
						
						println("</source>");
					}
					println("</flow>");
				}
				println("</results>");
			}
			
			if (outFilename != null) {
				try {
					wr.close();
				} catch (Exception ex) {
				}
			}
		}
		
		public String getMethodSignature(Stmt stmt) {
			// Returns the signature of a method, like: sendBroadcast(android.content.Intent)
			if (!stmt.containsInvokeExpr()) {
				return "Stmt(" + stmt.toString() + ")";
			}
			AbstractInvokeExpr ie = (AbstractInvokeExpr) stmt.getInvokeExpr();
			SootMethod meth = ie.getMethod();
			return meth.getSignature();
		
		}
		
		private static String getComponentTypeFromMethod(Stmt stmt) {
			// We want to know, if a method starts an Activity, a Service or a Broadcast Reciever, the easiest way to know, is simply to
			// check the method name.
			
			if (!stmt.containsInvokeExpr()) {
				return "";
			}

			AbstractInvokeExpr ie = (AbstractInvokeExpr) stmt.getInvokeExpr();
			SootMethod meth = ie.getMethod();

			if (meth.toString().indexOf("startActivity") != -1) {
				return "Activity";
			}

			if (meth.toString().indexOf("sendBroadcast") != -1 || meth.toString().indexOf("sendStickyBroadcast") != -1 || meth.toString().indexOf("sendOrderedBroadcast") != -1) {
				return "BroadcastReceiver";
			}

			if (meth.toString().indexOf("startService") != -1 || meth.toString().indexOf("bindService") != -1) {
				return "Service";
			}

			return "";
		}

		public static String escapeXML(Object obj) {
			return escapeXML(obj.toString(), "");
		}

		public static String escapeXML(String str, String retIfNull) {
			/*
			 * Based on
			 * http://www.docjar.com/html/api/org/apache/commons/lang/Entities
			 * .java.html
			 */
			if (str == null) {
				return retIfNull;
			}
			StringWriter writer = new StringWriter();

			int len = str.length();
			for (int i = 0; i < len; i++) {
				char c = str.charAt(i);
				if (c > 0x7F) {
					writer.write("&#");
					writer.write(Integer.toString(c, 10));
					writer.write(';');
				} else {
					switch ((byte) c) {
					case '&':
						writer.write("&amp;");
						break;
					case '<':
						writer.write("&lt;");
						break;
					case '>':
						writer.write("&gt;");
						break;
					case '"':
						writer.write("&quot;");
						break;
					case '\'':
						writer.write("&apos;");
						break;
					default:
						writer.write(c);
					}
				}
			}
			return writer.toString();
		}

		private void println(String string) {
			try {
				System.out.println(string);
				if (wr != null)
					wr.write(string + "\n");
			} catch (IOException ex) {
				// ignore
			}
		}

		private void print(String string) {
			try {
				System.out.println(string);
				if (wr != null)
					wr.write(string + "\n");
			}
			catch (IOException ex) {
				// ignore
			}
		}
	}
	
	static String command;
	static boolean generate = false;
	
	private static int timeout = -1;
	private static int sysTimeout = -1;
	
	private static boolean stopAfterFirstFlow = false;
	private static boolean implicitFlows = false;
	private static boolean staticTracking = true;
	private static boolean enableCallbacks = true;
	private static boolean enableExceptions = true;
	private static int accessPathLength = 5;
	private static LayoutMatchingMode layoutMatchingMode = LayoutMatchingMode.MatchSensitiveOnly;
	private static boolean flowSensitiveAliasing = true;
	private static boolean computeResultPaths = true;
	private static boolean aggressiveTaintWrapper = false;
	private static boolean librarySummaryTaintWrapper = false;
	private static String summaryPath = "";
	private static PathBuilder pathBuilder;
	private static String outFilename = null;
	
	private static CallgraphAlgorithm callgraphAlgorithm = CallgraphAlgorithm.AutomaticSelection;
	
	private static boolean DEBUG = false;

	private static IIPCManager ipcManager = null;
	public static void setIPCManager(IIPCManager ipcManager)
	{
		Test.ipcManager = ipcManager;
	}
	public static IIPCManager getIPCManager()
	{
		return Test.ipcManager;
	}
	
	/**
	 * @param args[0] = path to apk-file
	 * @param args[1] = path to android-dir (path/android-platforms/)
	 */
	public static void main(final String[] args) throws IOException, InterruptedException {
		if (args.length < 2) {
			printUsage();	
			return;
		}
		//start with cleanup:
		File outputDir = new File("JimpleOutput");
		if (outputDir.isDirectory()){
			boolean success = true;
			for(File f : outputDir.listFiles()){
				success = success && f.delete();
			}
			if(!success){
				System.err.println("Cleanup of output directory "+ outputDir + " failed!");
			}
			outputDir.delete();
		}
		
		// Parse additional command-line arguments
		if (!parseAdditionalOptions(args))
			return;
		if (!validateAdditionalOptions())
			return;
		
		List<String> apkFiles = new ArrayList<String>();
		File apkFile = new File(args[0]);
		String extension = apkFile.getName().substring(apkFile.getName().lastIndexOf("."));
		if (apkFile.isDirectory()) {
			String[] dirFiles = apkFile.list(new FilenameFilter() {
			
				@Override
				public boolean accept(File dir, String name) {
					return (name.endsWith(".apk"));
				}
			
			});
			for (String s : dirFiles)
				apkFiles.add(s);
		}
		else if (extension.equalsIgnoreCase(".txt")) {
			BufferedReader rdr = new BufferedReader(new FileReader(apkFile));
			String line = null;
			while ((line = rdr.readLine()) != null)
				apkFiles.add(line);
			rdr.close();
		}
		else if (extension.equalsIgnoreCase(".apk"))
			apkFiles.add(args[0]);
		else {
			System.err.println("Invalid input file format: " + extension);
			return;
		}

		for (final String fileName : apkFiles) {
			final String fullFilePath;
			
			// Directory handling
			if (apkFiles.size() > 1) {
				if (apkFile.isDirectory())
					fullFilePath = args[0] + File.separator + fileName;
				else
					fullFilePath = fileName;
				System.out.println("Analyzing file " + fullFilePath + "...");
				File flagFile = new File("_Run_" + new File(fileName).getName());
				if (flagFile.exists())
					continue;
				flagFile.createNewFile();
			}
			else
				fullFilePath = fileName;

			// Run the analysis
			if (timeout > 0)
				runAnalysisTimeout(fullFilePath, args[1]);
			else if (sysTimeout > 0)
				runAnalysisSysTimeout(fullFilePath, args[1]);
			else
				runAnalysis(fullFilePath, args[1]);

			System.gc();
		}
	}


	private static boolean parseAdditionalOptions(String[] args) {
		int i = 2;
		while (i < args.length) {
			if (args[i].equalsIgnoreCase("--timeout")) {
				timeout = Integer.valueOf(args[i+1]);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--systimeout")) {
				sysTimeout = Integer.valueOf(args[i+1]);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--singleflow")) {
				stopAfterFirstFlow = true;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--implicit")) {
				implicitFlows = true;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--nostatic")) {
				staticTracking = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--aplength")) {
				accessPathLength = Integer.valueOf(args[i+1]);
				i += 2;
			} 
			else if (args[i].equalsIgnoreCase("--out")) {
				outFilename = args[i + 1];
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--cgalgo")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("AUTO"))
					callgraphAlgorithm = CallgraphAlgorithm.AutomaticSelection;
				else if (algo.equalsIgnoreCase("CHA"))
					callgraphAlgorithm = CallgraphAlgorithm.CHA;
				else if (algo.equalsIgnoreCase("VTA"))
					callgraphAlgorithm = CallgraphAlgorithm.VTA;
				else if (algo.equalsIgnoreCase("RTA"))
					callgraphAlgorithm = CallgraphAlgorithm.RTA;
				else if (algo.equalsIgnoreCase("SPARK"))
					callgraphAlgorithm = CallgraphAlgorithm.SPARK;
				else {
					System.err.println("Invalid callgraph algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--nocallbacks")) {
				enableCallbacks = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--noexceptions")) {
				enableExceptions = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--layoutmode")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("NONE"))
					layoutMatchingMode = LayoutMatchingMode.NoMatch;
				else if (algo.equalsIgnoreCase("PWD"))
					layoutMatchingMode = LayoutMatchingMode.MatchSensitiveOnly;
				else if (algo.equalsIgnoreCase("ALL"))
					layoutMatchingMode = LayoutMatchingMode.MatchAll;
				else {
					System.err.println("Invalid layout matching mode");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--aliasflowins")) {
				flowSensitiveAliasing = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--nopaths")) {
				computeResultPaths = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--aggressivetw")) {
				aggressiveTaintWrapper = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--pathalgo")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("CONTEXTSENSITIVE"))
					pathBuilder = PathBuilder.ContextSensitive;
				else if (algo.equalsIgnoreCase("CONTEXTINSENSITIVE"))
					pathBuilder = PathBuilder.ContextInsensitive;
				else if (algo.equalsIgnoreCase("SOURCESONLY"))
					pathBuilder = PathBuilder.ContextInsensitiveSourceFinder;
				else {
					System.err.println("Invalid path reconstruction algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--libsumtw")) {
				librarySummaryTaintWrapper = true;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--summarypath")) {
				summaryPath = args[i + 1];
				i += 2;
			}
			else
				i++;
		}
		return true;
	}
	
	private static boolean validateAdditionalOptions() {
		if (timeout > 0 && sysTimeout > 0) {
			return false;
		}
		if (!flowSensitiveAliasing && callgraphAlgorithm != CallgraphAlgorithm.OnDemand
				&& callgraphAlgorithm != CallgraphAlgorithm.AutomaticSelection) {
			System.err.println("Flow-insensitive aliasing can only be configured for callgraph "
					+ "algorithms that support this choice.");
			return false;
		}
		if (librarySummaryTaintWrapper && summaryPath.isEmpty()) {
			System.err.println("Summary path must be specified when using library summaries");
			return false;
		}
		return true;
	}
	
	private static void runAnalysisTimeout(final String fileName, final String androidJar) {
		FutureTask<InfoflowResults> task = new FutureTask<InfoflowResults>(new Callable<InfoflowResults>() {

			@Override
			public InfoflowResults call() throws Exception {
				
				final BufferedWriter wr = new BufferedWriter(new FileWriter("_out_" + new File(fileName).getName() + ".txt"));
				try {
					final long beforeRun = System.nanoTime();
					wr.write("Running data flow analysis...\n");
					final InfoflowResults res = runAnalysis(fileName, androidJar);
					wr.write("Analysis has run for " + (System.nanoTime() - beforeRun) / 1E9 + " seconds\n");
					
					wr.flush();
					return res;
				}
				finally {
					if (wr != null)
						wr.close();
				}
			}
			
		});
		ExecutorService executor = Executors.newFixedThreadPool(1);
		executor.execute(task);
		
		try {
			System.out.println("Running infoflow task...");
			task.get(timeout, TimeUnit.MINUTES);
		} catch (ExecutionException e) {
			System.err.println("Infoflow computation failed: " + e.getMessage());
			e.printStackTrace();
		} catch (TimeoutException e) {
			System.err.println("Infoflow computation timed out: " + e.getMessage());
			e.printStackTrace();
		} catch (InterruptedException e) {
			System.err.println("Infoflow computation interrupted: " + e.getMessage());
			e.printStackTrace();
		}
		
		// Make sure to remove leftovers
		executor.shutdown();		
	}

	private static void runAnalysisSysTimeout(final String fileName, final String androidJar) {
		String classpath = System.getProperty("java.class.path");
		String javaHome = System.getProperty("java.home");
		String executable = "/usr/bin/timeout";
		String[] command = new String[] { executable,
				"-s", "KILL",
				sysTimeout + "m",
				javaHome + "/bin/java",
				"-cp", classpath,
				"soot.jimple.infoflow.android.TestApps.Test",
				fileName,
				androidJar,
				stopAfterFirstFlow ? "--singleflow" : "--nosingleflow",
				implicitFlows ? "--implicit" : "--noimplicit",
				staticTracking ? "--static" : "--nostatic", 
				"--aplength", Integer.toString(accessPathLength),
				"--cgalgo", callgraphAlgorithmToString(callgraphAlgorithm),
				enableCallbacks ? "--callbacks" : "--nocallbacks",
				enableExceptions ? "--exceptions" : "--noexceptions",
				"--layoutmode", layoutMatchingModeToString(layoutMatchingMode),
				flowSensitiveAliasing ? "--aliasflowsens" : "--aliasflowins",
				computeResultPaths ? "--paths" : "--nopaths",
				aggressiveTaintWrapper ? "--aggressivetw" : "--nonaggressivetw",
				"--pathalgo", pathAlgorithmToString(pathBuilder) };
		System.out.println("Running command: " + executable + " " + command);
		try {
			ProcessBuilder pb = new ProcessBuilder(command);
			pb.redirectOutput(new File("_out_" + new File(fileName).getName() + ".txt"));
			pb.redirectError(new File("err_" + new File(fileName).getName() + ".txt"));
			Process proc = pb.start();
			proc.waitFor();
		} catch (IOException ex) {
			System.err.println("Could not execute timeout command: " + ex.getMessage());
			ex.printStackTrace();
		} catch (InterruptedException ex) {
			System.err.println("Process was interrupted: " + ex.getMessage());
			ex.printStackTrace();
		}
	}
	
	private static String callgraphAlgorithmToString(CallgraphAlgorithm algorihm) {
		switch (algorihm) {
			case AutomaticSelection:
				return "AUTO";
			case CHA:
				return "CHA";
			case VTA:
				return "VTA";
			case RTA:
				return "RTA";
			case SPARK:
				return "SPARK";
			default:
				return "unknown";
		}
	}

	private static String layoutMatchingModeToString(LayoutMatchingMode mode) {
		switch (mode) {
			case NoMatch:
				return "NONE";
			case MatchSensitiveOnly:
				return "PWD";
			case MatchAll:
				return "ALL";
			default:
				return "unknown";
		}
	}
	
	private static String pathAlgorithmToString(PathBuilder pathBuilder) {
		switch (pathBuilder) {
			case ContextSensitive:
				return "CONTEXTSENSITIVE";
			case ContextInsensitive :
				return "CONTEXTINSENSITIVE";
			case ContextInsensitiveSourceFinder :
				return "SOURCESONLY";
			default :
				return "UNKNOWN";
		}
	}
	
	private static InfoflowResults runAnalysis(final String fileName, final String androidJar) {
		try {
			final long beforeRun = System.nanoTime();

			final SetupApplication app;
			if (null == ipcManager)
			{
				app = new SetupApplication(androidJar, fileName);
			}
			else
			{
				app = new SetupApplication(androidJar, fileName, ipcManager);
			}

			app.setStopAfterFirstFlow(stopAfterFirstFlow);
			app.setEnableImplicitFlows(implicitFlows);
			app.setEnableStaticFieldTracking(staticTracking);
			app.setEnableCallbacks(enableCallbacks);
			app.setEnableExceptionTracking(enableExceptions);
			app.setAccessPathLength(accessPathLength);
			app.setLayoutMatchingMode(layoutMatchingMode);
			app.setFlowSensitiveAliasing(flowSensitiveAliasing);
			
			final ITaintPropagationWrapper taintWrapper;
			if (librarySummaryTaintWrapper) {
				taintWrapper = createLibrarySummaryTW();
			}
			else {
				final EasyTaintWrapper easyTaintWrapper;
				if (new File("../soot-infoflow/EasyTaintWrapperSource.txt").exists())
					easyTaintWrapper = new EasyTaintWrapper("../soot-infoflow/EasyTaintWrapperSource.txt");
				else
					easyTaintWrapper = new EasyTaintWrapper("EasyTaintWrapperSource.txt");
				easyTaintWrapper.setAggressiveMode(aggressiveTaintWrapper);
				taintWrapper = easyTaintWrapper;
			}
			app.setTaintWrapper(taintWrapper);
			app.calculateSourcesSinksEntrypoints("SourcesAndSinks.txt");
			
			if (DEBUG) {
				app.printEntrypoints();
				app.printSinks();
				app.printSources();
			}
				
			System.out.println("Running data flow analysis...");
			MyResultsAvailableHandler handler = new MyResultsAvailableHandler();
			handler.appPkgName = app.getSourceSinkManager().getAppPackageName();
			
			final InfoflowResults res = app.runInfoflow(handler);
			System.out.println("Analysis has run for " + (System.nanoTime() - beforeRun) / 1E9 + " seconds");
			return res;
		} catch (IOException ex) {
			System.err.println("Could not read file: " + ex.getMessage());
			ex.printStackTrace();
			throw new RuntimeException(ex);
		} catch (XmlPullParserException ex) {
			System.err.println("Could not read Android manifest file: " + ex.getMessage());
			ex.printStackTrace();
			throw new RuntimeException(ex);
		}
	}
	
	/**
	 * Creates the taint wrapper for using library summaries
	 * @return The taint wrapper for using library summaries
	 * @throws IOException Thrown if one of the required files could not be read
	 */
	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static ITaintPropagationWrapper createLibrarySummaryTW()
			throws IOException {
		try {
			Class clzLazySummary = Class.forName("soot.jimple.infoflow.methodSummary.data.impl.LazySummary");
			
			Object lazySummary = clzLazySummary.getConstructor(File.class).newInstance(new File(summaryPath));
			
			ITaintPropagationWrapper summaryWrapper = (ITaintPropagationWrapper) Class.forName
					("soot.jimple.infoflow.methodSummary.taintWrappers.SummaryTaintWrapper").getConstructor
					(clzLazySummary).newInstance(lazySummary);
			
			final TaintWrapperSet taintWrapperSet = new TaintWrapperSet();
			taintWrapperSet.addWrapper(summaryWrapper);
			taintWrapperSet.addWrapper(new EasyTaintWrapper("EasyTaintWrapperConversion.txt"));
			return taintWrapperSet;
		}
		catch (ClassNotFoundException | NoSuchMethodException ex) {
			System.err.println("Could not find library summary classes: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
		catch (InvocationTargetException ex) {
			System.err.println("Could not initialize library summaries: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
		catch (IllegalAccessException | InstantiationException ex) {
			System.err.println("Internal error in library summary initialization: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
	}

	private static void printUsage() {
		System.out.println("FlowDroid (c) Secure Software Engineering Group @ EC SPRIDE");
		System.out.println();
		System.out.println("Incorrect arguments: [0] = apk-file, [1] = android-jar-directory");
		System.out.println("Optional further parameters:");
		System.out.println("\t--TIMEOUT n Time out after n seconds");
		System.out.println("\t--SYSTIMEOUT n Hard time out (kill process) after n seconds, Unix only");
		System.out.println("\t--SINGLEFLOW Stop after finding first leak");
		System.out.println("\t--IMPLICIT Enable implicit flows");
		System.out.println("\t--NOSTATIC Disable static field tracking");
		System.out.println("\t--NOEXCEPTIONS Disable exception tracking");
		System.out.println("\t--APLENGTH n Set access path length to n");
		System.out.println("\t--CGALGO x Use callgraph algorithm x");
		System.out.println("\t--NOCALLBACKS Disable callback analysis");
		System.out.println("\t--LAYOUTMODE x Set UI control analysis mode to x");
		System.out.println("\t--ALIASFLOWINS Use a flow insensitive alias search");
		System.out.println("\t--NOPATHS Do not compute result paths");
		System.out.println("\t--AGGRESSIVETW Use taint wrapper in aggressive mode");
		System.out.println("\t--out <filename.xml>");
		System.out.println("\t--PATHALGO Use path reconstruction algorithm x");
		System.out.println("\t--LIBSUMTW Use library summary taint wrapper");
		System.out.println("\t--SUMMARYPATH Path to library summaries");
		System.out.println();
		System.out.println("Supported callgraph algorithms: AUTO, CHA, RTA, VTA, SPARK");
		System.out.println("Supported layout mode algorithms: NONE, PWD, ALL");
		System.out.println("Supported path algorithms: CONTEXTSENSITIVE, CONTEXTINSENSITIVE, SOURCESONLY");
	}

}
