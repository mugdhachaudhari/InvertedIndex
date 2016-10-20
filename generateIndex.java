import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.io.ObjectInputStream.GetField;
import java.lang.reflect.Array;
import java.net.URL;
import java.net.URLEncoder;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.PriorityQueue;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;


class MinHeap {
	private HeapStruct[] heap;
	private int size;
	private int maxSize;
	private static final int FRONT = 1;

	public MinHeap(int maxSize){
	    this.heap = new HeapStruct[maxSize+1];
	    heap[0] = null;
	    this.size = 0;
	}

	private int getParent(int position){
	    return position/2;
	}

	private int getLeftChild(int position){
	    return 2*position;
	}

	private int getRightChild(int position){
	    return 2*position+1;
	}

	private void swap(int position1, int position2){
		HeapStruct temp = heap[position1];
	    heap[position1] = heap[position2];
	    heap[position2] = temp;
	}

	private boolean isLeaf(int position){

	    if(position > size/2){
	        return true;
	    }
	    return false;
	}

	public void insert(HeapStruct data){
	    heap[++size] = data;
	    int currentItem = size;
	    while(size > 1 && getParent(currentItem) != 0 && heap[getParent(currentItem)].compareTo(heap[currentItem]) > 0 ){
	        swap(getParent(currentItem),currentItem);
	        currentItem = getParent(currentItem);
	    }
	}

	public HeapStruct delete(){
		HeapStruct itemPopped = heap[FRONT];
	    heap[FRONT] = heap[size--];
	    heapify(FRONT);
	    return itemPopped;
	}
	
	public HeapStruct getFront() {
		return heap[FRONT];
	}
	
	public int getSize(){
		return size;
	}
	
	public void replaceFront(HeapStruct data) {
		heap[FRONT] = data;
		heapify(FRONT);
	}

	public void heapify(int position){
	    if(isLeaf(position)){
	        return;
	    }
	    if (getRightChild(position) > size) {
	    	if ( (heap[position].compareTo(heap[getLeftChild(position)]) > 0)) {
	    		swap(position, getLeftChild(position));
	    	}
	    } else {
		    if ( (heap[position].compareTo(heap[getLeftChild(position)]) > 0) || (heap[position].compareTo(heap[getRightChild(position)]) > 0)){

		        if(heap[getLeftChild(position)].compareTo(heap[getRightChild(position)]) < 0){
		            swap(position , getLeftChild(position));
		            heapify(getLeftChild(position));
		        }
		        else{
		            swap(position , getRightChild(position));
		            heapify(getRightChild(position));
		        }
		    }
	    }
	}

	@Override
	public String toString(){
	    StringBuilder output = new StringBuilder();
	    for(int i=1; i<= size/2; i++){
	        output.append("Parent :"+ heap[i]);
	        String left = heap[getLeftChild(i)].toString();
	        output.append("LeftChild : "+left + "\n"); 
	        String right = null;
	        if (getRightChild(i) <= size) {
	        	right = heap[getRightChild(i)].toString();
	        	output.append("RightChild :"+ right + "\n");
	        }
	        
	    }
	    return output.toString();
	}
}


class PostingNext {
	public int nextId;
	public int position;
	
	public PostingNext(int nextId, int position) {
		this.nextId = nextId;
		this.position = position;
	}
}

class HeapStruct implements Comparable<HeapStruct> {
	public String term;
	public int fileNr;
	public int docFreq, postingPtr;
	public byte[] posting;
	public String postingAscii;
	
	public HeapStruct(String term, int fileNr, int docFreq, int postingPtr, byte[] posting) {
		this.term = term;
		this.fileNr = fileNr;
		this.docFreq = docFreq;
		this.postingPtr = postingPtr;
		this.posting = posting;
	}
	
	public HeapStruct(String term, int fileNr, int docFreq, int postingPtr, String posting) {
		this.term = term;
		this.fileNr = fileNr;
		this.docFreq = docFreq;
		this.postingPtr = postingPtr;
		this.postingAscii = posting;
	}
	
	public int compareTo(HeapStruct obj) {
		if (this.term.compareTo(obj.term) > 0) {
			return 1;
		} else if (this.term.compareTo(obj.term) < 0) {
			return -1;
		} else if (this.fileNr > obj.fileNr) {
			return 1;
		} else {
			return -1;
		}
	}
	
	public String toString() {
		if (generateIndex.mode.equals("ascii")) {
			return(term + " , " + fileNr + " , " + docFreq + " , " + postingPtr + " , " + postingAscii);
		} else {
			return(term + " , " + fileNr + " , " + docFreq + " , " + postingPtr + " , " + Arrays.toString(posting));
		}

	}
}

class MergeBuffer {
	public BufferedOutputStream bo;
	public BufferedWriter boAscii;
	public BufferedWriter bw;
	public BufferedWriter docUrlbw;
	public String prevTerm;
	public int prevDocFreq;
	public byte[] prevInv;
	public String prevInvAscii;
	public int glbPosition = 0;
	public Integer prevDocId = 0;
	
	public MergeBuffer(BufferedOutputStream bo, BufferedWriter bw, BufferedWriter docUrlbw) {
		this.bo = bo;
		this.bw = bw;
		this.docUrlbw = docUrlbw;
	}
	
	public MergeBuffer(BufferedWriter bo, BufferedWriter bw, BufferedWriter docUrlbw) {
		this.boAscii = bo;
		this.bw = bw;
		this.docUrlbw = docUrlbw;
	}
}

class partialIndexBuffer {
	public BufferedInputStream invIndBStream;
	public BufferedReader invIndBStreamAscii;
	public BufferedReader lexBufReader;
	public String[] prevLex;
	
	public partialIndexBuffer(BufferedInputStream ds, BufferedReader br) {
		invIndBStream = ds;
		lexBufReader = br;
		try {
			String prevLexStr = br.readLine();
			if (prevLexStr != null) {
				prevLex = prevLexStr.trim().split("\t");
			}
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
	}
	
	public partialIndexBuffer(BufferedReader ds, BufferedReader br) {
		invIndBStreamAscii = ds;
		lexBufReader = br;
		try {
			String prevLexStr = br.readLine();
			if (prevLexStr != null) {
				prevLex = prevLexStr.trim().split("\t");
			}
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
	}
}

public class generateIndex {
	private static HashMap<Integer, Integer> fileDocMap;
	private static boolean isDebug = true;
	private static int maxFilesToMerge;
	private static StringBuilder sb;
//	public static String mode = "ascii";
//	public static String mode = "binary";
	public static String mode;
	private static int glbPosition = 0;
	public static String splCh = "ability.";
	
	private static void initialize(int max, String fileFormat) {
		maxFilesToMerge = max;
		mode = fileFormat;
	}
	
	// Return path of directory containing data and index files
	private static String returnPath(String pathStr) {
		URL url = Thread.currentThread().getContextClassLoader().getResource("");
		String FileName = url.getPath() + java.io.File.separator + pathStr;
		File Dir = new File(FileName);
		if (!Dir.exists()) {
			try {
				Dir.mkdir();
			} catch (Exception e) {
				System.out.println(e);
				System.out.println("Error in creating Directory " + pathStr);
				System.exit(1);
			}
		}
		return FileName;
	}
	
//	Given a byte array convert it to integer
	private static int convertByteToNumber(ArrayList<Byte> bt) {
		int power = bt.size() - 1;
		int x = 0;
		for (Byte b :bt) {
			if (b >= 0) {
				x += b;
			} else {
				x += (Math.pow(128, power--)* (byte) (b & ~(1 << 7)));
			}
		}
		return x;
	}
	
//	Get next number from byte array and return posiiton to read number appearing after this number
	private static PostingNext getNextId(byte[] posting, int i) {
		int id;
		if (posting[i] >= 0) {
			id = posting[i];
			i++;
		} else {
			ArrayList<Byte> bt = new ArrayList<Byte>();
			while(posting[i] < 0) {
				bt.add(posting[i]);
				i++;
			}
			bt.add(posting[i]);
			i++;
			id = convertByteToNumber(bt);
		}
		return new PostingNext(id, i);
	}
	

	
	// list data files from given directory
	private static File[] listFiles(String dirName) {
		File dir = new File(dirName);
		// Filter to select only data files
		FilenameFilter fileNameFilter = new FilenameFilter() {
			@Override
			public boolean accept(File dir, String name) {
				if (mode.equals("ascii")) {
					if (name.startsWith("invIndexAscii_")) {
						return true;
					}
				} else {
					if (name.startsWith("invIndex_")) {
						return true;
					}
				}
				return false;
			}
		};
		return dir.listFiles(fileNameFilter);
	}
	
//	Return next record to be entered in MinHeap.
	private static HeapStruct nextRecord(int i, ArrayList<partialIndexBuffer> partialData) {
		partialIndexBuffer ib = partialData.get(i);
		if (ib.prevLex == null) {
			return null;
		}
		HeapStruct t = null;
		try {
			String nextLexStr = ib.lexBufReader.readLine();
			String[] nextLex = null;
			int nextPos = 0;
			byte[] b = null;
			String s = null;
			
			if (nextLexStr != null) {
				
				nextLex = nextLexStr.trim().split("\t");
				nextPos = Integer.parseInt(nextLex[1]); //Include this index
				if (mode.equals("ascii")) {
					s = ib.invIndBStreamAscii.readLine();
				} else {
					b = new byte[nextPos - Integer.parseInt(ib.prevLex[1])];
					ib.invIndBStream.read(b);
				}

			} else {
				if (mode.equals("ascii")) {
					s = ib.invIndBStreamAscii.readLine();
				} else{
					ArrayList<Byte> ba = new ArrayList<Byte>();
					int sb;
					while((sb = ib.invIndBStream.read()) != -1) {
						ba.add((byte)sb);
					}
					b = new byte[ba.size()];
					int bi = 0;
					for (Byte x : ba) {
						b[bi] = x.valueOf(x);
						bi++;
					}
				}

			}

			if (mode.equals("ascii")) {
				t = new HeapStruct(ib.prevLex[0], i, Integer.parseInt(ib.prevLex[2]), Integer.parseInt(ib.prevLex[1]), s);
			} else {
				t = new HeapStruct(ib.prevLex[0], i, Integer.parseInt(ib.prevLex[2]), Integer.parseInt(ib.prevLex[1]), b);
			}

			ib.prevLex = nextLex;

		} catch (Exception e) {
			System.out.println(e);
			e.printStackTrace();
			System.out.println("Error in reading lexbuffer or invIndBuffer");
			System.exit(1);
		}
		return t;
		
		
	}
	
//	Read index data files from given list and merge them to subindex as per maxFilesToMerge size till there is only one
//	set of files left(Inverted Index, Lexicon and Page table)
	private static void readInvIndexFiles(File[] listF) {
		int numMergePass = 0;
		int maxDegree = maxFilesToMerge;
		int numOutFiles = 0;
		while (numOutFiles != 1) {
			if (numOutFiles == 0 && numMergePass > 0) {
				break;
			}
			File[] listOfFiles;
			numOutFiles = 0;
			int ttlReadFiles = 0;
			if (numMergePass == 0) {
				listOfFiles = listF;
			} else {
				int mo = numMergePass - 1;
				listOfFiles = listFiles(returnPath("MergeOut_" + mo));
			}
			System.out.println("Pass number is " + numMergePass);
			while(ttlReadFiles < listOfFiles.length) {
				
				sb = new StringBuilder();
				
				MergeBuffer mergeB = null;
				ArrayList<partialIndexBuffer> partialData = new ArrayList<partialIndexBuffer>();
				int docIdStart = 0;
				fileDocMap = new HashMap<Integer, Integer>();
				try {
//					DocUrl Out filr
					String outDocUrlFile = returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "docUrl_" + numOutFiles;
					OutputStream outDocUrlStream = new FileOutputStream(outDocUrlFile);
					OutputStream outDocUrlgzipStream = new GZIPOutputStream(outDocUrlStream);
					Writer outDocUrldecoder = new OutputStreamWriter(outDocUrlgzipStream);
					
					if (mode.equals("ascii")) {
//						Inv Index Ascii out file
						String outInvAIndexFile = returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "invIndexAscii_" + numOutFiles;
						OutputStream outInvAIndStream = new FileOutputStream(outInvAIndexFile);
						OutputStream outInvAIndgzipStream = new GZIPOutputStream(outInvAIndStream);
						Writer outdecoderIA = new OutputStreamWriter(outInvAIndgzipStream);
						
//						Lexicon structure Ascii out file
						String outLexAFile = returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "lexiconAscii_" + numOutFiles;
						OutputStream outLexAStream = new FileOutputStream(outLexAFile);
						OutputStream outLexgzipAStream = new GZIPOutputStream(outLexAStream);
						Writer outdecoderA = new OutputStreamWriter(outLexgzipAStream);
						mergeB = new MergeBuffer(new BufferedWriter(outdecoderIA), 
								new BufferedWriter(outdecoderA), new BufferedWriter(outDocUrldecoder));
					} else {
//						Inv Index out file
						String outInvIndexFile = returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "invIndex_" + numOutFiles;
						OutputStream outInvIndStream = new FileOutputStream(outInvIndexFile);
						OutputStream outInvIndgzipStream = new GZIPOutputStream(outInvIndStream);

//						Lexicon structure out file
						String outLexFile = returnPath("MergeOut_" + numMergePass) + java.io.File.separator + "lexicon_" + numOutFiles;
						OutputStream outLexStream = new FileOutputStream(outLexFile);
						OutputStream outLexgzipStream = new GZIPOutputStream(outLexStream);
						Writer outdecoder = new OutputStreamWriter(outLexgzipStream);
						
						mergeB = new MergeBuffer(new BufferedOutputStream(outInvIndgzipStream), 
								new BufferedWriter(outdecoder), new BufferedWriter(outDocUrldecoder));
						
					}
				} catch (Exception e) {
					System.out.println(e);
					System.out.println("Error in creating mergeout files " + numOutFiles + " for Merge Pass " + numMergePass );
					System.exit(1);
				}

				int degree = 0;
				for (degree = 0; degree < maxDegree; degree++) {
					try {
						if (ttlReadFiles >= listOfFiles.length) {
							break;
						}
//						Get lexicon structure file name for corresponding inverted index file name
						String parentPath = listOfFiles[ttlReadFiles].getParent();
						String invIndFileNm = listOfFiles[ttlReadFiles].getName();
						if(isDebug) {System.out.println(" Processing files " + invIndFileNm); }
						String cnt = invIndFileNm.substring(invIndFileNm.indexOf('_') + 1);
						
//						Add inverted index buffer to data input stream array list
						InputStream fileStream = new FileInputStream(listOfFiles[ttlReadFiles]);
						InputStream gzipStream = new GZIPInputStream(fileStream);
						File lexFile = null;
						if (mode.equals("ascii")) {
							lexFile = new File(parentPath + java.io.File.separator + "lexiconAscii_" + cnt);
						} else {
							lexFile = new File(parentPath + java.io.File.separator + "lexicon_" + cnt);
						}
//						Add lexicon structure file to buffered reader arraylist
						InputStream fileStreamL = new FileInputStream(lexFile);
						InputStream gzipStreamL = new GZIPInputStream(fileStreamL);
						Reader decoder = new InputStreamReader(gzipStreamL);
						
						File docUrlFile = new File(parentPath + java.io.File.separator + "docUrl_" + cnt);
//						Write DocUrl File
						InputStream fileStreamD = new FileInputStream(docUrlFile);
						InputStream gzipStreamD = new GZIPInputStream(fileStreamD);
						Reader decoderD = new InputStreamReader(gzipStreamD);
						fileDocMap.put(degree, docIdStart);
						docIdStart = writeDocUrlFile(new BufferedReader(decoderD), docIdStart, mergeB.docUrlbw);
						if (mode.equals("ascii")) {
							Reader decoderA = new InputStreamReader(gzipStream);
							partialData.add(new partialIndexBuffer(new BufferedReader(decoderA, 65536), new BufferedReader(decoder)));
						} else {
							partialData.add(new partialIndexBuffer(new BufferedInputStream(gzipStream, 65536), new BufferedReader(decoder)));
						}

					} catch (Exception e) {
						System.out.println(e);
						System.out.println("Error in reading file " + listOfFiles[ttlReadFiles]);
						System.exit(1);
					}
					ttlReadFiles++;
				}
				if (degree == 0) {
					break;
				}
				MinHeap heap = new MinHeap(degree);
				
				for (int i = 0; i < degree; i++) {
					HeapStruct nxtR = nextRecord(i, partialData);
//					System.out.println(nxtR.toString());
					if (nxtR == null) {
						//Reduce size of heap
						heap.delete();
					} else {
						heap.insert(nxtR);
					}
				}
//				Merge files
				while (heap.getSize() > 0) {
//					Write minimum record to output
					HeapStruct front= heap.getFront();
//					Uncomment Later
					writeRecord(front, mergeB);
//					replace minumum in heap by next record in that file
					HeapStruct nxtR = nextRecord(front.fileNr, partialData);
					if (nxtR == null) {
						heap.delete();
					} else {
						heap.replaceFront(nxtR);
					}

				}
//				To write last record
				writeRecord(null, mergeB);
			
//				Write records in file. Can include in writeRecord method
				for (int i = 0; i < degree; i++) {
					try {
						if (mode.equals("ascii")) {
							partialData.get(i).invIndBStreamAscii.close();
						} else {
							partialData.get(i).invIndBStream.close();
						}
						partialData.get(i).lexBufReader.close();
					} catch (Exception e) {
						System.out.println(e);
						System.out.println("Error in closing partial inv index files");
						System.exit(1);
					}
				}
				
				try {
					if (mode.equals("ascii")) {
						mergeB.boAscii.close();
						glbPosition = 0;
					} else {
						mergeB.bo.close();
					}
					mergeB.bw.close();
					mergeB.docUrlbw.close();
				} catch (Exception e) {
					System.out.println(e);
					System.out.println("Error in closing out merge file");
					System.exit(1);
				}

				numOutFiles++;
			}
			numMergePass++;
		}

	}

//	For binary files update doc ID in posting according to merge file Page table numbers.
	private static byte[] updateDocIdPosting(HeapStruct data, MergeBuffer mergeB) {
		int i = 0;
		int docId, docFreq, newDocId = 0;
		int lastPos = 0;
		int sumDocId = 0;
		int docIdStart = 0;
		int prevDocId = mergeB.prevDocId;
		byte[] tempBytes = null;
		ArrayList<Byte> ba = new ArrayList<Byte>();
//		System.out.println("Doc freq is " + data.docFreq);
		for (int j = 0; j < data.docFreq; j++) {
			PostingNext pd = getNextId(data.posting, i);
			docId = pd.nextId;
			sumDocId += docId;
			int docIdPos = pd.position; //First docId position ended one position beofre it
//			System.out.println("Doc Id is " + docId);
//			System.out.println("i is " + pd.position);
//			Comment Remove try and catch block
			try {
				pd = getNextId(data.posting, pd.position);
			} catch (Exception e) {
				System.out.println("Exception " + e);
			}

			docFreq = pd.nextId;
			i = pd.position;
			if (j == 0) {
				lastPos = docIdPos;
				docIdStart = fileDocMap.get(data.fileNr);
				newDocId = docId + docIdStart;
				tempBytes = generatePostings.getByteCode(newDocId - prevDocId);
			}
		}
		byte[] finalB = new byte[tempBytes.length + data.posting.length - lastPos];
		System.arraycopy(tempBytes, 0, finalB, 0, tempBytes.length);
		System.arraycopy(data.posting, lastPos, finalB, tempBytes.length, data.posting.length - lastPos);
		mergeB.prevDocId = sumDocId + docIdStart;
		return finalB;
		
		
	}

	private static String updateDocIdPostingAscii(HeapStruct data, MergeBuffer mergeB) {
		int docId, docFreq, newDocId = 0;
		int lastPos = 0;
		int sumDocId = 0;
		int docIdStart = 0;
		int prevDocId = mergeB.prevDocId;
		String[] s = null;
		try {
			s = data.postingAscii.split(",");
		} catch (Exception e) {
			System.out.println("Exception " + e);
		}
		
		docIdStart = fileDocMap.get(data.fileNr);
		StringBuilder rs = new StringBuilder();
		for (int i = 0; i < s.length; i++) {
			String[] p = s[i].split(":");
			sumDocId += Integer.parseInt(p[0]);
			if (i == 0) {
				newDocId = Integer.parseInt(p[0]) + docIdStart;
				s[i] = newDocId  + ":" + p[1];
			}
			rs.append(s[i] + ",");
		}

		mergeB.prevDocId = sumDocId + docIdStart;
		return rs.toString();
	}
	
	private static int writeDocUrlFile(BufferedReader docUrlFile, int docIdStart, BufferedWriter docUrlBw) {
		String line = null;
		int id = 0;
		try {
			while ((line = docUrlFile.readLine()) != null) {
				String[] s = line.trim().split("\t", 2);
				id = docIdStart + Integer.parseInt(s[0]);
				docUrlBw.write(id + "\t" + s[1] + "\n");
			}
			return id;
		} catch (Exception e) {
			System.out.println(e);
			System.out.println("Error in reading docUrl file");
			System.exit(1);
		}
		return id;

	}
	
	private static void writeRecord(HeapStruct data, MergeBuffer mergeB) {
		if (data != null) {
			if (mergeB.prevTerm == null) {
				mergeB.prevTerm = data.term;
				mergeB.prevDocFreq = data.docFreq;
				mergeB.prevDocId = 0;
				if (mode.equals("ascii")) {
					mergeB.prevInvAscii = updateDocIdPostingAscii(data, mergeB);
				} else {
					mergeB.prevInv = updateDocIdPosting(data, mergeB);
				}
			} else {
				if (data.term.equals(mergeB.prevTerm)) {
					mergeB.prevDocFreq += data.docFreq;
					if (mode.equals("ascii")) {
						String s = updateDocIdPostingAscii(data, mergeB);
						StringBuilder st = new StringBuilder();
						st.append(mergeB.prevInvAscii);
						st.append(s);
						mergeB.prevInvAscii = st.toString();
					} else {
						byte[] updPosting = updateDocIdPosting(data, mergeB);
						byte[] newUpd = new byte[mergeB.prevInv.length + updPosting.length];
						System.arraycopy(mergeB.prevInv, 0, newUpd, 0, mergeB.prevInv.length);
						System.arraycopy(updPosting, 0, newUpd, mergeB.prevInv.length, updPosting.length);
						mergeB.prevInv = newUpd; 
					}

//					Merge two terms
				} else {
					try {
//						write prev term to buffer
						String s = mergeB.prevTerm + "\t" + mergeB.glbPosition + "\t" + mergeB.prevDocFreq + "\n";
						mergeB.bw.write(s);
//						Update docIds
						if (mode.equals("ascii")) {
							mergeB.boAscii.write(mergeB.prevInvAscii + "\n"); 
						} else {
							mergeB.bo.write(mergeB.prevInv); 
						}

					} catch (Exception e) {
						System.out.println(e);
						System.out.println("Error in writing merge file");
						System.exit(1);
					}
//					Make current term as previous term
					mergeB.prevTerm = data.term;
					mergeB.prevDocFreq = data.docFreq;
					mergeB.prevDocId = 0;
					if (mode.equals("ascii")) {
//						Update glbPosition
						mergeB.glbPosition += 1;
						mergeB.prevInvAscii = updateDocIdPostingAscii(data, mergeB);
					} else {
//						Update glbPosition
						mergeB.glbPosition += mergeB.prevInv.length;
						mergeB.prevInv = updateDocIdPosting(data, mergeB);
					}
				}
			}
		} else {
//			write prev record directly
			try {
//				write prev term to buffer
				mergeB.bw.write(mergeB.prevTerm + "\t" + mergeB.glbPosition + "\t" + mergeB.prevDocFreq + "\n");
//				Update docIds
				if (mode.equals("ascii")) {
					mergeB.boAscii.write(mergeB.prevInvAscii + "\n");
				} else {
					mergeB.bo.write(mergeB.prevInv); 
				}
			} catch (Exception e) {
				System.out.println(e);
				System.out.println("Error in writing merge file");
				System.exit(1);
			}
		}
		
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		System.out.println("Start Time " + Calendar.getInstance().getTime());
		int maxFilestoMerge = 10;
		String fileFormat = "binary";
		initialize(maxFilestoMerge, fileFormat);
		readInvIndexFiles(listFiles(returnPath("PostingOutput")));
		System.out.println("End Time " + Calendar.getInstance().getTime());
	}
}
