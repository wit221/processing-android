package processing.core;

import android.app.Activity;
import android.app.ActivityManager;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.pm.ConfigurationInfo;
import android.content.res.AssetManager;
import android.content.res.Configuration;
import android.graphics.Typeface;
import android.net.Uri;
import android.opengl.GLSurfaceView;
import android.os.Bundle;
import android.os.Handler;
import android.text.format.Time;
import android.util.DisplayMetrics;
import android.util.Log;
import android.view.Display;
import android.view.MotionEvent;
import android.view.SurfaceHolder;
import android.view.SurfaceHolder.Callback;
import android.view.SurfaceView;
import android.view.View;
import android.view.Window;
import android.view.WindowManager;
import android.widget.LinearLayout;
import android.widget.RelativeLayout;
import android.widget.RelativeLayout.LayoutParams;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URLDecoder;
import java.net.URLEncoder;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Random;
import java.util.StringTokenizer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;
import org.apache.http.HttpEntity;
import org.apache.http.HttpResponse;
import org.apache.http.client.HttpClient;
import org.apache.http.client.methods.HttpGet;
import org.apache.http.client.methods.HttpUriRequest;
import org.apache.http.impl.client.DefaultHttpClient;
import processing.data.Table;
import processing.data.XML;
import processing.event.Event;
import processing.event.MouseEvent;
import processing.event.TouchEvent;
import processing.opengl.PGL;
import processing.opengl.PGLES;
import processing.opengl.PGraphics2D;
import processing.opengl.PGraphics3D;
import processing.opengl.PGraphicsOpenGL;
import processing.opengl.PShader;

public class PApplet
  extends Activity
  implements PConstants, Runnable
{
  public static final String ARGS_BGCOLOR = "--bgcolor";
  public static final String ARGS_DISPLAY = "--display";
  public static final String ARGS_EDITOR_LOCATION = "--editor-location";
  public static final String ARGS_EXCLUSIVE = "--exclusive";
  public static final String ARGS_EXTERNAL = "--external";
  public static final String ARGS_HIDE_STOP = "--hide-stop";
  public static final String ARGS_LOCATION = "--location";
  public static final String ARGS_PRESENT = "--present";
  public static final String ARGS_SKETCH_FOLDER = "--sketch-path";
  public static final String ARGS_STOP_COLOR = "--stop-color";
  public static final boolean DEBUG = false;
  static final String ERROR_MIN_MAX = "Cannot use min() or max() on an empty array.";
  public static final String EXTERNAL_MOVE = "__MOVE__";
  public static final String EXTERNAL_STOP = "__STOP__";
  public static final byte[] ICON_IMAGE = { 71, 73, 70, 56, 57, 97, 16, 0, 16, 0, -77, 0, 0, 0, 0, 0, -1, -1, -1, 12, 12, 13, -15, -15, -14, 45, 57, 74, 54, 80, 111, 47, 71, 97, 62, 88, 117, 1, 14, 27, 7, 41, 73, 15, 52, 85, 2, 31, 55, 4, 54, 94, 18, 69, 109, 37, 87, 126, -1, -1, -1, 33, -7, 4, 1, 0, 0, 15, 0, 44, 0, 0, 0, 0, 16, 0, 16, 0, 0, 4, 122, -16, -107, 114, -86, -67, 83, 30, -42, 26, -17, -100, -45, 56, -57, -108, 48, 40, 122, -90, 104, 67, -91, -51, 32, -53, 77, -78, -100, 47, -86, 12, 76, -110, -20, -74, -101, 97, -93, 27, 40, 20, -65, 65, 48, -111, 99, -20, -112, -117, -123, -47, -105, 24, 114, -112, 74, 69, 84, 25, 93, 88, -75, 9, 46, 2, 49, 88, -116, -67, 7, -19, -83, 60, 38, 3, -34, 2, 66, -95, 27, -98, 13, 4, -17, 55, 33, 109, 11, 11, -2, -128, 121, 123, 62, 91, 120, -128, 127, 122, 115, 102, 2, 119, 0, -116, -113, -119, 6, 102, 121, -108, -126, 5, 18, 6, 4, -102, -101, -100, 114, 15, 17, 0, 59 };
  static final int META_CTRL_ON = 4096;
  static final int META_META_ON = 65536;
  static final int PERLIN_SIZE = 4095;
  static final int PERLIN_YWRAP = 16;
  static final int PERLIN_YWRAPB = 4;
  static final int PERLIN_ZWRAP = 256;
  static final int PERLIN_ZWRAPB = 8;
  private static NumberFormat float_nf;
  private static boolean float_nf_commas;
  private static int float_nf_left;
  private static int float_nf_right;
  private static NumberFormat int_nf;
  private static boolean int_nf_commas;
  private static int int_nf_digits;
  protected static HashMap<String, Pattern> matchPatterns;
  protected static Time time = new Time();
  public int displayHeight;
  public int displayWidth;
  protected int dmouseX;
  protected int dmouseY;
  protected int emouseX;
  protected int emouseY;
  InternalEventQueue eventQueue = new InternalEventQueue();
  protected boolean exitCalled;
  boolean external = false;
  public boolean finished;
  public boolean focused = false;
  public int frameCount;
  public float frameRate = 10.0F;
  protected long frameRateLastNanos = 0L;
  protected long frameRatePeriod = 16666666L;
  protected float frameRateTarget = 60.0F;
  public PGraphics g;
  Handler handler;
  public int height;
  Random internalRandom;
  public char key;
  public int keyCode;
  public boolean keyPressed;
  protected boolean looping;
  long millisOffset = System.currentTimeMillis();
  int motionPointerId;
  public boolean mousePressed;
  public int mouseX;
  public int mouseY;
  protected boolean paused;
  float[] perlin;
  Random perlinRandom;
  int perlin_PI;
  int perlin_TWOPI;
  float perlin_amp_falloff = 0.5F;
  float[] perlin_cosTable;
  int perlin_octaves = 4;
  public int[] pixels;
  public int pmouseX;
  public int pmouseY;
  protected boolean redraw;
  HashMap<String, RegisteredMethods> registerMap = new HashMap();
  volatile int requestImageCount;
  public int requestImageMax = 4;
  public String sketchPath;
  protected boolean surfaceChanged;
  protected boolean surfaceReady;
  protected SurfaceView surfaceView;
  Thread thread;
  protected boolean viewFocused = false;
  public int width;
  protected boolean windowFocused = false;
  
  public static final float abs(float paramFloat)
  {
    float f = paramFloat;
    if (paramFloat < 0.0F) {
      f = -paramFloat;
    }
    return f;
  }
  
  public static final int abs(int paramInt)
  {
    int i = paramInt;
    if (paramInt < 0) {
      i = -paramInt;
    }
    return i;
  }
  
  public static final float acos(float paramFloat)
  {
    return (float)Math.acos(paramFloat);
  }
  
  public static Object append(Object paramObject1, Object paramObject2)
  {
    int i = Array.getLength(paramObject1);
    paramObject1 = expand(paramObject1, i + 1);
    Array.set(paramObject1, i, paramObject2);
    return paramObject1;
  }
  
  public static byte[] append(byte[] paramArrayOfByte, byte paramByte)
  {
    paramArrayOfByte = expand(paramArrayOfByte, paramArrayOfByte.length + 1);
    paramArrayOfByte[(paramArrayOfByte.length - 1)] = paramByte;
    return paramArrayOfByte;
  }
  
  public static char[] append(char[] paramArrayOfChar, char paramChar)
  {
    paramArrayOfChar = expand(paramArrayOfChar, paramArrayOfChar.length + 1);
    paramArrayOfChar[(paramArrayOfChar.length - 1)] = paramChar;
    return paramArrayOfChar;
  }
  
  public static float[] append(float[] paramArrayOfFloat, float paramFloat)
  {
    paramArrayOfFloat = expand(paramArrayOfFloat, paramArrayOfFloat.length + 1);
    paramArrayOfFloat[(paramArrayOfFloat.length - 1)] = paramFloat;
    return paramArrayOfFloat;
  }
  
  public static int[] append(int[] paramArrayOfInt, int paramInt)
  {
    paramArrayOfInt = expand(paramArrayOfInt, paramArrayOfInt.length + 1);
    paramArrayOfInt[(paramArrayOfInt.length - 1)] = paramInt;
    return paramArrayOfInt;
  }
  
  public static String[] append(String[] paramArrayOfString, String paramString)
  {
    paramArrayOfString = expand(paramArrayOfString, paramArrayOfString.length + 1);
    paramArrayOfString[(paramArrayOfString.length - 1)] = paramString;
    return paramArrayOfString;
  }
  
  public static void arrayCopy(Object paramObject1, int paramInt1, Object paramObject2, int paramInt2, int paramInt3)
  {
    System.arraycopy(paramObject1, paramInt1, paramObject2, paramInt2, paramInt3);
  }
  
  public static void arrayCopy(Object paramObject1, Object paramObject2)
  {
    System.arraycopy(paramObject1, 0, paramObject2, 0, Array.getLength(paramObject1));
  }
  
  public static void arrayCopy(Object paramObject1, Object paramObject2, int paramInt)
  {
    System.arraycopy(paramObject1, 0, paramObject2, 0, paramInt);
  }
  
  public static final float asin(float paramFloat)
  {
    return (float)Math.asin(paramFloat);
  }
  
  public static final float atan(float paramFloat)
  {
    return (float)Math.atan(paramFloat);
  }
  
  public static final float atan2(float paramFloat1, float paramFloat2)
  {
    return (float)Math.atan2(paramFloat1, paramFloat2);
  }
  
  public static final String binary(byte paramByte)
  {
    return binary(paramByte, 8);
  }
  
  public static final String binary(char paramChar)
  {
    return binary(paramChar, 16);
  }
  
  public static final String binary(int paramInt)
  {
    return binary(paramInt, 32);
  }
  
  public static final String binary(int paramInt1, int paramInt2)
  {
    String str = Integer.toBinaryString(paramInt1);
    paramInt1 = paramInt2;
    if (paramInt2 > 32) {
      paramInt1 = 32;
    }
    paramInt2 = str.length();
    if (paramInt2 > paramInt1) {
      return str.substring(paramInt2 - paramInt1);
    }
    if (paramInt2 < paramInt1) {
      return "00000000000000000000000000000000".substring(32 - (paramInt1 - paramInt2)) + str;
    }
    return str;
  }
  
  public static int blendColor(int paramInt1, int paramInt2, int paramInt3)
  {
    return PImage.blendColor(paramInt1, paramInt2, paramInt3);
  }
  
  public static final int ceil(float paramFloat)
  {
    return (int)Math.ceil(paramFloat);
  }
  
  public static String checkExtension(String paramString)
  {
    String str = paramString;
    if (paramString.toLowerCase().endsWith(".gz")) {
      str = paramString.substring(0, paramString.length() - 3);
    }
    int i = str.lastIndexOf('.');
    if (i != -1) {
      return str.substring(i + 1).toLowerCase();
    }
    return null;
  }
  
  public static Object concat(Object paramObject1, Object paramObject2)
  {
    Object localObject = paramObject1.getClass().getComponentType();
    int i = Array.getLength(paramObject1);
    int j = Array.getLength(paramObject2);
    localObject = Array.newInstance((Class)localObject, i + j);
    System.arraycopy(paramObject1, 0, localObject, 0, i);
    System.arraycopy(paramObject2, 0, localObject, i, j);
    return localObject;
  }
  
  public static byte[] concat(byte[] paramArrayOfByte1, byte[] paramArrayOfByte2)
  {
    byte[] arrayOfByte = new byte[paramArrayOfByte1.length + paramArrayOfByte2.length];
    System.arraycopy(paramArrayOfByte1, 0, arrayOfByte, 0, paramArrayOfByte1.length);
    System.arraycopy(paramArrayOfByte2, 0, arrayOfByte, paramArrayOfByte1.length, paramArrayOfByte2.length);
    return arrayOfByte;
  }
  
  public static char[] concat(char[] paramArrayOfChar1, char[] paramArrayOfChar2)
  {
    char[] arrayOfChar = new char[paramArrayOfChar1.length + paramArrayOfChar2.length];
    System.arraycopy(paramArrayOfChar1, 0, arrayOfChar, 0, paramArrayOfChar1.length);
    System.arraycopy(paramArrayOfChar2, 0, arrayOfChar, paramArrayOfChar1.length, paramArrayOfChar2.length);
    return arrayOfChar;
  }
  
  public static float[] concat(float[] paramArrayOfFloat1, float[] paramArrayOfFloat2)
  {
    float[] arrayOfFloat = new float[paramArrayOfFloat1.length + paramArrayOfFloat2.length];
    System.arraycopy(paramArrayOfFloat1, 0, arrayOfFloat, 0, paramArrayOfFloat1.length);
    System.arraycopy(paramArrayOfFloat2, 0, arrayOfFloat, paramArrayOfFloat1.length, paramArrayOfFloat2.length);
    return arrayOfFloat;
  }
  
  public static int[] concat(int[] paramArrayOfInt1, int[] paramArrayOfInt2)
  {
    int[] arrayOfInt = new int[paramArrayOfInt1.length + paramArrayOfInt2.length];
    System.arraycopy(paramArrayOfInt1, 0, arrayOfInt, 0, paramArrayOfInt1.length);
    System.arraycopy(paramArrayOfInt2, 0, arrayOfInt, paramArrayOfInt1.length, paramArrayOfInt2.length);
    return arrayOfInt;
  }
  
  public static String[] concat(String[] paramArrayOfString1, String[] paramArrayOfString2)
  {
    String[] arrayOfString = new String[paramArrayOfString1.length + paramArrayOfString2.length];
    System.arraycopy(paramArrayOfString1, 0, arrayOfString, 0, paramArrayOfString1.length);
    System.arraycopy(paramArrayOfString2, 0, arrayOfString, paramArrayOfString1.length, paramArrayOfString2.length);
    return arrayOfString;
  }
  
  public static boolean[] concat(boolean[] paramArrayOfBoolean1, boolean[] paramArrayOfBoolean2)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfBoolean1.length + paramArrayOfBoolean2.length];
    System.arraycopy(paramArrayOfBoolean1, 0, arrayOfBoolean, 0, paramArrayOfBoolean1.length);
    System.arraycopy(paramArrayOfBoolean2, 0, arrayOfBoolean, paramArrayOfBoolean1.length, paramArrayOfBoolean2.length);
    return arrayOfBoolean;
  }
  
  public static final float constrain(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    if (paramFloat1 < paramFloat2) {
      return paramFloat2;
    }
    if (paramFloat1 > paramFloat3) {
      return paramFloat3;
    }
    return paramFloat1;
  }
  
  public static final int constrain(int paramInt1, int paramInt2, int paramInt3)
  {
    if (paramInt1 < paramInt2) {
      return paramInt2;
    }
    if (paramInt1 > paramInt3) {
      return paramInt3;
    }
    return paramInt1;
  }
  
  public static final float cos(float paramFloat)
  {
    return (float)Math.cos(paramFloat);
  }
  
  public static InputStream createInput(File paramFile)
  {
    if (paramFile == null) {
      throw new IllegalArgumentException("File passed to createInput() was null");
    }
    try
    {
      Object localObject = new FileInputStream(paramFile);
      if (paramFile.getName().toLowerCase().endsWith(".gz"))
      {
        localObject = new GZIPInputStream((InputStream)localObject);
        return (InputStream)localObject;
      }
      return (InputStream)localObject;
    }
    catch (IOException localIOException)
    {
      System.err.println("Could not createInput() for " + paramFile);
      localIOException.printStackTrace();
    }
    return null;
  }
  
  public static OutputStream createOutput(File paramFile)
  {
    try
    {
      FileOutputStream localFileOutputStream = new FileOutputStream(paramFile);
      if (paramFile.getName().toLowerCase().endsWith(".gz"))
      {
        paramFile = new GZIPOutputStream(localFileOutputStream);
        return paramFile;
      }
      return localFileOutputStream;
    }
    catch (IOException paramFile)
    {
      paramFile.printStackTrace();
    }
    return null;
  }
  
  public static void createPath(File paramFile)
  {
    try
    {
      Object localObject = paramFile.getParent();
      if (localObject != null)
      {
        localObject = new File((String)localObject);
        if (!((File)localObject).exists()) {
          ((File)localObject).mkdirs();
        }
      }
      return;
    }
    catch (SecurityException localSecurityException)
    {
      System.err.println("You don't have permissions to create " + paramFile.getAbsolutePath());
    }
  }
  
  public static void createPath(String paramString)
  {
    createPath(new File(paramString));
  }
  
  public static BufferedReader createReader(File paramFile)
  {
    for (;;)
    {
      try
      {
        Object localObject = new FileInputStream(paramFile);
        if (paramFile.getName().toLowerCase().endsWith(".gz"))
        {
          localObject = new GZIPInputStream((InputStream)localObject);
          localObject = createReader((InputStream)localObject);
          return (BufferedReader)localObject;
        }
      }
      catch (Exception localException)
      {
        if (paramFile == null) {
          throw new RuntimeException("File passed to createReader() was null");
        }
        localException.printStackTrace();
        throw new RuntimeException("Couldn't create a reader for " + paramFile.getAbsolutePath());
      }
    }
  }
  
  public static BufferedReader createReader(InputStream paramInputStream)
  {
    try
    {
      paramInputStream = new InputStreamReader(paramInputStream, "UTF-8");
      return new BufferedReader(paramInputStream);
    }
    catch (UnsupportedEncodingException paramInputStream)
    {
      for (;;)
      {
        paramInputStream = null;
      }
    }
  }
  
  public static PrintWriter createWriter(File paramFile)
  {
    for (;;)
    {
      try
      {
        Object localObject = new FileOutputStream(paramFile);
        if (paramFile.getName().toLowerCase().endsWith(".gz"))
        {
          localObject = new GZIPOutputStream((OutputStream)localObject);
          localObject = createWriter((OutputStream)localObject);
          return (PrintWriter)localObject;
        }
      }
      catch (Exception localException)
      {
        if (paramFile == null) {
          throw new RuntimeException("File passed to createWriter() was null");
        }
        localException.printStackTrace();
        throw new RuntimeException("Couldn't create a writer for " + paramFile.getAbsolutePath());
      }
    }
  }
  
  public static PrintWriter createWriter(OutputStream paramOutputStream)
  {
    try
    {
      paramOutputStream = new PrintWriter(new OutputStreamWriter(new BufferedOutputStream(paramOutputStream, 8192), "UTF-8"));
      return paramOutputStream;
    }
    catch (UnsupportedEncodingException paramOutputStream) {}
    return null;
  }
  
  public static int day()
  {
    time.setToNow();
    return time.monthDay;
  }
  
  public static final float degrees(float paramFloat)
  {
    return 57.295776F * paramFloat;
  }
  
  public static final float dist(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    return sqrt(sq(paramFloat3 - paramFloat1) + sq(paramFloat4 - paramFloat2));
  }
  
  public static final float dist(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    return sqrt(sq(paramFloat4 - paramFloat1) + sq(paramFloat5 - paramFloat2) + sq(paramFloat6 - paramFloat3));
  }
  
  public static Process exec(String[] paramArrayOfString)
  {
    try
    {
      Process localProcess = Runtime.getRuntime().exec(paramArrayOfString);
      return localProcess;
    }
    catch (Exception localException)
    {
      localException.printStackTrace();
      throw new RuntimeException("Could not open " + join(paramArrayOfString, ' '));
    }
  }
  
  public static final float exp(float paramFloat)
  {
    return (float)Math.exp(paramFloat);
  }
  
  public static Object expand(Object paramObject)
  {
    return expand(paramObject, Array.getLength(paramObject) << 1);
  }
  
  public static Object expand(Object paramObject, int paramInt)
  {
    Object localObject = Array.newInstance(paramObject.getClass().getComponentType(), paramInt);
    System.arraycopy(paramObject, 0, localObject, 0, Math.min(Array.getLength(paramObject), paramInt));
    return localObject;
  }
  
  public static byte[] expand(byte[] paramArrayOfByte)
  {
    return expand(paramArrayOfByte, paramArrayOfByte.length << 1);
  }
  
  public static byte[] expand(byte[] paramArrayOfByte, int paramInt)
  {
    byte[] arrayOfByte = new byte[paramInt];
    System.arraycopy(paramArrayOfByte, 0, arrayOfByte, 0, Math.min(paramInt, paramArrayOfByte.length));
    return arrayOfByte;
  }
  
  public static char[] expand(char[] paramArrayOfChar)
  {
    return expand(paramArrayOfChar, paramArrayOfChar.length << 1);
  }
  
  public static char[] expand(char[] paramArrayOfChar, int paramInt)
  {
    char[] arrayOfChar = new char[paramInt];
    System.arraycopy(paramArrayOfChar, 0, arrayOfChar, 0, Math.min(paramInt, paramArrayOfChar.length));
    return arrayOfChar;
  }
  
  public static float[] expand(float[] paramArrayOfFloat)
  {
    return expand(paramArrayOfFloat, paramArrayOfFloat.length << 1);
  }
  
  public static float[] expand(float[] paramArrayOfFloat, int paramInt)
  {
    float[] arrayOfFloat = new float[paramInt];
    System.arraycopy(paramArrayOfFloat, 0, arrayOfFloat, 0, Math.min(paramInt, paramArrayOfFloat.length));
    return arrayOfFloat;
  }
  
  public static int[] expand(int[] paramArrayOfInt)
  {
    return expand(paramArrayOfInt, paramArrayOfInt.length << 1);
  }
  
  public static int[] expand(int[] paramArrayOfInt, int paramInt)
  {
    int[] arrayOfInt = new int[paramInt];
    System.arraycopy(paramArrayOfInt, 0, arrayOfInt, 0, Math.min(paramInt, paramArrayOfInt.length));
    return arrayOfInt;
  }
  
  public static String[] expand(String[] paramArrayOfString)
  {
    return expand(paramArrayOfString, paramArrayOfString.length << 1);
  }
  
  public static String[] expand(String[] paramArrayOfString, int paramInt)
  {
    String[] arrayOfString = new String[paramInt];
    System.arraycopy(paramArrayOfString, 0, arrayOfString, 0, Math.min(paramInt, paramArrayOfString.length));
    return arrayOfString;
  }
  
  public static PImage[] expand(PImage[] paramArrayOfPImage)
  {
    return expand(paramArrayOfPImage, paramArrayOfPImage.length << 1);
  }
  
  public static PImage[] expand(PImage[] paramArrayOfPImage, int paramInt)
  {
    PImage[] arrayOfPImage = new PImage[paramInt];
    System.arraycopy(paramArrayOfPImage, 0, arrayOfPImage, 0, Math.min(paramInt, paramArrayOfPImage.length));
    return arrayOfPImage;
  }
  
  public static boolean[] expand(boolean[] paramArrayOfBoolean)
  {
    return expand(paramArrayOfBoolean, paramArrayOfBoolean.length << 1);
  }
  
  public static boolean[] expand(boolean[] paramArrayOfBoolean, int paramInt)
  {
    boolean[] arrayOfBoolean = new boolean[paramInt];
    System.arraycopy(paramArrayOfBoolean, 0, arrayOfBoolean, 0, Math.min(paramInt, paramArrayOfBoolean.length));
    return arrayOfBoolean;
  }
  
  public static final int floor(float paramFloat)
  {
    return (int)Math.floor(paramFloat);
  }
  
  public static String getExtension(String paramString)
  {
    String str = paramString.toLowerCase();
    int i = paramString.lastIndexOf('.');
    if (i == -1) {}
    str = str.substring(i + 1);
    i = str.indexOf('?');
    paramString = str;
    if (i != -1) {
      paramString = str.substring(0, i);
    }
    return paramString;
  }
  
  public static final String hex(byte paramByte)
  {
    return hex(paramByte, 2);
  }
  
  public static final String hex(char paramChar)
  {
    return hex(paramChar, 4);
  }
  
  public static final String hex(int paramInt)
  {
    return hex(paramInt, 8);
  }
  
  public static final String hex(int paramInt1, int paramInt2)
  {
    String str = Integer.toHexString(paramInt1).toUpperCase();
    paramInt1 = paramInt2;
    if (paramInt2 > 8) {
      paramInt1 = 8;
    }
    paramInt2 = str.length();
    if (paramInt2 > paramInt1) {
      return str.substring(paramInt2 - paramInt1);
    }
    if (paramInt2 < paramInt1) {
      return "00000000".substring(8 - (paramInt1 - paramInt2)) + str;
    }
    return str;
  }
  
  public static int hour()
  {
    time.setToNow();
    return time.hour;
  }
  
  public static String join(String[] paramArrayOfString, char paramChar)
  {
    return join(paramArrayOfString, String.valueOf(paramChar));
  }
  
  public static String join(String[] paramArrayOfString, String paramString)
  {
    StringBuffer localStringBuffer = new StringBuffer();
    int i = 0;
    while (i < paramArrayOfString.length)
    {
      if (i != 0) {
        localStringBuffer.append(paramString);
      }
      localStringBuffer.append(paramArrayOfString[i]);
      i += 1;
    }
    return localStringBuffer.toString();
  }
  
  public static final float lerp(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return (paramFloat2 - paramFloat1) * paramFloat3 + paramFloat1;
  }
  
  public static int lerpColor(int paramInt1, int paramInt2, float paramFloat, int paramInt3)
  {
    return PGraphics.lerpColor(paramInt1, paramInt2, paramFloat, paramInt3);
  }
  
  public static byte[] loadBytes(File paramFile)
  {
    return loadBytes(createInput(paramFile));
  }
  
  public static byte[] loadBytes(InputStream paramInputStream)
  {
    try
    {
      paramInputStream = new BufferedInputStream(paramInputStream);
      ByteArrayOutputStream localByteArrayOutputStream = new ByteArrayOutputStream();
      for (int i = paramInputStream.read(); i != -1; i = paramInputStream.read()) {
        localByteArrayOutputStream.write(i);
      }
      paramInputStream = localByteArrayOutputStream.toByteArray();
      return paramInputStream;
    }
    catch (IOException paramInputStream)
    {
      paramInputStream.printStackTrace();
    }
    return null;
  }
  
  public static String[] loadStrings(BufferedReader paramBufferedReader)
  {
    for (;;)
    {
      Object localObject;
      int i;
      String str;
      try
      {
        localObject = new String[100];
        i = 0;
        str = paramBufferedReader.readLine();
        if (str != null)
        {
          if (i == localObject.length)
          {
            String[] arrayOfString = new String[i << 1];
            System.arraycopy(localObject, 0, arrayOfString, 0, i);
            localObject = arrayOfString;
          }
        }
        else
        {
          paramBufferedReader.close();
          if (i == localObject.length) {
            return (String[])localObject;
          }
          paramBufferedReader = new String[i];
          System.arraycopy(localObject, 0, paramBufferedReader, 0, i);
          return paramBufferedReader;
        }
      }
      catch (IOException paramBufferedReader)
      {
        paramBufferedReader.printStackTrace();
        return null;
      }
      localObject[i] = str;
      i += 1;
    }
  }
  
  public static String[] loadStrings(File paramFile)
  {
    paramFile = createInput(paramFile);
    if (paramFile != null) {
      return loadStrings(paramFile);
    }
    return null;
  }
  
  public static String[] loadStrings(InputStream paramInputStream)
  {
    for (;;)
    {
      int i;
      String str;
      try
      {
        BufferedReader localBufferedReader = new BufferedReader(new InputStreamReader(paramInputStream, "UTF-8"));
        paramInputStream = new String[100];
        i = 0;
        str = localBufferedReader.readLine();
        String[] arrayOfString;
        if (str != null)
        {
          if (i == paramInputStream.length)
          {
            arrayOfString = new String[i << 1];
            System.arraycopy(paramInputStream, 0, arrayOfString, 0, i);
            paramInputStream = arrayOfString;
          }
        }
        else
        {
          localBufferedReader.close();
          if (i == paramInputStream.length) {
            return paramInputStream;
          }
          arrayOfString = new String[i];
          System.arraycopy(paramInputStream, 0, arrayOfString, 0, i);
          return arrayOfString;
        }
      }
      catch (IOException paramInputStream)
      {
        paramInputStream.printStackTrace();
        return null;
      }
      paramInputStream[i] = str;
      i += 1;
    }
  }
  
  public static final float log(float paramFloat)
  {
    return (float)Math.log(paramFloat);
  }
  
  public static final float mag(float paramFloat1, float paramFloat2)
  {
    return (float)Math.sqrt(paramFloat1 * paramFloat1 + paramFloat2 * paramFloat2);
  }
  
  public static final float mag(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return (float)Math.sqrt(paramFloat1 * paramFloat1 + paramFloat2 * paramFloat2 + paramFloat3 * paramFloat3);
  }
  
  public static void main(String[] paramArrayOfString) {}
  
  public static final float map(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    return (paramFloat5 - paramFloat4) * ((paramFloat1 - paramFloat2) / (paramFloat3 - paramFloat2)) + paramFloat4;
  }
  
  public static String[] match(String paramString1, String paramString2)
  {
    Matcher localMatcher = matchPattern(paramString2).matcher(paramString1);
    if (localMatcher.find())
    {
      int j = localMatcher.groupCount() + 1;
      paramString2 = new String[j];
      int i = 0;
      for (;;)
      {
        paramString1 = paramString2;
        if (i >= j) {
          break;
        }
        paramString2[i] = localMatcher.group(i);
        i += 1;
      }
    }
    paramString1 = null;
    return paramString1;
  }
  
  public static String[][] matchAll(String paramString1, String paramString2)
  {
    paramString1 = matchPattern(paramString2).matcher(paramString1);
    ArrayList localArrayList = new ArrayList();
    int j = paramString1.groupCount() + 1;
    while (paramString1.find())
    {
      paramString2 = new String[j];
      i = 0;
      while (i < j)
      {
        paramString2[i] = paramString1.group(i);
        i += 1;
      }
      localArrayList.add(paramString2);
    }
    if (localArrayList.isEmpty())
    {
      paramString1 = (String[][])null;
      return paramString1;
    }
    paramString2 = (String[][])Array.newInstance(String.class, new int[] { localArrayList.size(), j });
    int i = 0;
    for (;;)
    {
      paramString1 = paramString2;
      if (i >= paramString2.length) {
        break;
      }
      paramString2[i] = ((String[])(String[])localArrayList.get(i));
      i += 1;
    }
  }
  
  static Pattern matchPattern(String paramString)
  {
    Pattern localPattern1 = null;
    if (matchPatterns == null) {
      matchPatterns = new HashMap();
    }
    for (;;)
    {
      Pattern localPattern2 = localPattern1;
      if (localPattern1 == null)
      {
        if (matchPatterns.size() == 10) {
          matchPatterns.clear();
        }
        localPattern2 = Pattern.compile(paramString, 40);
        matchPatterns.put(paramString, localPattern2);
      }
      return localPattern2;
      localPattern1 = (Pattern)matchPatterns.get(paramString);
    }
  }
  
  public static final float max(float paramFloat1, float paramFloat2)
  {
    if (paramFloat1 > paramFloat2) {
      return paramFloat1;
    }
    return paramFloat2;
  }
  
  public static final float max(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    float f;
    if (paramFloat1 > paramFloat2)
    {
      f = paramFloat3;
      if (paramFloat1 > paramFloat3) {
        f = paramFloat1;
      }
    }
    do
    {
      return f;
      f = paramFloat3;
    } while (paramFloat2 <= paramFloat3);
    return paramFloat2;
  }
  
  public static final float max(float[] paramArrayOfFloat)
  {
    if (paramArrayOfFloat.length == 0) {
      throw new ArrayIndexOutOfBoundsException("Cannot use min() or max() on an empty array.");
    }
    float f1 = paramArrayOfFloat[0];
    int i = 1;
    while (i < paramArrayOfFloat.length)
    {
      float f2 = f1;
      if (paramArrayOfFloat[i] > f1) {
        f2 = paramArrayOfFloat[i];
      }
      i += 1;
      f1 = f2;
    }
    return f1;
  }
  
  public static final int max(int paramInt1, int paramInt2)
  {
    if (paramInt1 > paramInt2) {
      return paramInt1;
    }
    return paramInt2;
  }
  
  public static final int max(int paramInt1, int paramInt2, int paramInt3)
  {
    int i;
    if (paramInt1 > paramInt2)
    {
      i = paramInt3;
      if (paramInt1 > paramInt3) {
        i = paramInt1;
      }
    }
    do
    {
      return i;
      i = paramInt3;
    } while (paramInt2 <= paramInt3);
    return paramInt2;
  }
  
  public static final int max(int[] paramArrayOfInt)
  {
    if (paramArrayOfInt.length == 0) {
      throw new ArrayIndexOutOfBoundsException("Cannot use min() or max() on an empty array.");
    }
    int j = paramArrayOfInt[0];
    int i = 1;
    while (i < paramArrayOfInt.length)
    {
      int k = j;
      if (paramArrayOfInt[i] > j) {
        k = paramArrayOfInt[i];
      }
      i += 1;
      j = k;
    }
    return j;
  }
  
  public static final float min(float paramFloat1, float paramFloat2)
  {
    if (paramFloat1 < paramFloat2) {
      return paramFloat1;
    }
    return paramFloat2;
  }
  
  public static final float min(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    float f;
    if (paramFloat1 < paramFloat2)
    {
      f = paramFloat3;
      if (paramFloat1 < paramFloat3) {
        f = paramFloat1;
      }
    }
    do
    {
      return f;
      f = paramFloat3;
    } while (paramFloat2 >= paramFloat3);
    return paramFloat2;
  }
  
  public static final float min(float[] paramArrayOfFloat)
  {
    if (paramArrayOfFloat.length == 0) {
      throw new ArrayIndexOutOfBoundsException("Cannot use min() or max() on an empty array.");
    }
    float f1 = paramArrayOfFloat[0];
    int i = 1;
    while (i < paramArrayOfFloat.length)
    {
      float f2 = f1;
      if (paramArrayOfFloat[i] < f1) {
        f2 = paramArrayOfFloat[i];
      }
      i += 1;
      f1 = f2;
    }
    return f1;
  }
  
  public static final int min(int paramInt1, int paramInt2)
  {
    if (paramInt1 < paramInt2) {
      return paramInt1;
    }
    return paramInt2;
  }
  
  public static final int min(int paramInt1, int paramInt2, int paramInt3)
  {
    int i;
    if (paramInt1 < paramInt2)
    {
      i = paramInt3;
      if (paramInt1 < paramInt3) {
        i = paramInt1;
      }
    }
    do
    {
      return i;
      i = paramInt3;
    } while (paramInt2 >= paramInt3);
    return paramInt2;
  }
  
  public static final int min(int[] paramArrayOfInt)
  {
    if (paramArrayOfInt.length == 0) {
      throw new ArrayIndexOutOfBoundsException("Cannot use min() or max() on an empty array.");
    }
    int j = paramArrayOfInt[0];
    int i = 1;
    while (i < paramArrayOfInt.length)
    {
      int k = j;
      if (paramArrayOfInt[i] < j) {
        k = paramArrayOfInt[i];
      }
      i += 1;
      j = k;
    }
    return j;
  }
  
  public static int minute()
  {
    time.setToNow();
    return time.minute;
  }
  
  public static int month()
  {
    time.setToNow();
    return time.month + 1;
  }
  
  public static String nf(float paramFloat, int paramInt1, int paramInt2)
  {
    if ((float_nf != null) && (float_nf_left == paramInt1) && (float_nf_right == paramInt2) && (!float_nf_commas)) {
      return float_nf.format(paramFloat);
    }
    float_nf = NumberFormat.getInstance();
    float_nf.setGroupingUsed(false);
    float_nf_commas = false;
    if (paramInt1 != 0) {
      float_nf.setMinimumIntegerDigits(paramInt1);
    }
    if (paramInt2 != 0)
    {
      float_nf.setMinimumFractionDigits(paramInt2);
      float_nf.setMaximumFractionDigits(paramInt2);
    }
    float_nf_left = paramInt1;
    float_nf_right = paramInt2;
    return float_nf.format(paramFloat);
  }
  
  public static String nf(int paramInt1, int paramInt2)
  {
    if ((int_nf != null) && (int_nf_digits == paramInt2) && (!int_nf_commas)) {
      return int_nf.format(paramInt1);
    }
    int_nf = NumberFormat.getInstance();
    int_nf.setGroupingUsed(false);
    int_nf_commas = false;
    int_nf.setMinimumIntegerDigits(paramInt2);
    int_nf_digits = paramInt2;
    return int_nf.format(paramInt1);
  }
  
  public static String[] nf(float[] paramArrayOfFloat, int paramInt1, int paramInt2)
  {
    String[] arrayOfString = new String[paramArrayOfFloat.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nf(paramArrayOfFloat[i], paramInt1, paramInt2);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String[] nf(int[] paramArrayOfInt, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfInt.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nf(paramArrayOfInt[i], paramInt);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String nfc(float paramFloat, int paramInt)
  {
    if ((float_nf != null) && (float_nf_left == 0) && (float_nf_right == paramInt) && (float_nf_commas)) {
      return float_nf.format(paramFloat);
    }
    float_nf = NumberFormat.getInstance();
    float_nf.setGroupingUsed(true);
    float_nf_commas = true;
    if (paramInt != 0)
    {
      float_nf.setMinimumFractionDigits(paramInt);
      float_nf.setMaximumFractionDigits(paramInt);
    }
    float_nf_left = 0;
    float_nf_right = paramInt;
    return float_nf.format(paramFloat);
  }
  
  public static String nfc(int paramInt)
  {
    if ((int_nf != null) && (int_nf_digits == 0) && (int_nf_commas)) {
      return int_nf.format(paramInt);
    }
    int_nf = NumberFormat.getInstance();
    int_nf.setGroupingUsed(true);
    int_nf_commas = true;
    int_nf.setMinimumIntegerDigits(0);
    int_nf_digits = 0;
    return int_nf.format(paramInt);
  }
  
  public static String[] nfc(float[] paramArrayOfFloat, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfFloat.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nfc(paramArrayOfFloat[i], paramInt);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String[] nfc(int[] paramArrayOfInt)
  {
    String[] arrayOfString = new String[paramArrayOfInt.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nfc(paramArrayOfInt[i]);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String nfp(float paramFloat, int paramInt1, int paramInt2)
  {
    if (paramFloat < 0.0F) {
      return nf(paramFloat, paramInt1, paramInt2);
    }
    return '+' + nf(paramFloat, paramInt1, paramInt2);
  }
  
  public static String nfp(int paramInt1, int paramInt2)
  {
    if (paramInt1 < 0) {
      return nf(paramInt1, paramInt2);
    }
    return '+' + nf(paramInt1, paramInt2);
  }
  
  public static String[] nfp(float[] paramArrayOfFloat, int paramInt1, int paramInt2)
  {
    String[] arrayOfString = new String[paramArrayOfFloat.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nfp(paramArrayOfFloat[i], paramInt1, paramInt2);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String[] nfp(int[] paramArrayOfInt, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfInt.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nfp(paramArrayOfInt[i], paramInt);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String nfs(float paramFloat, int paramInt1, int paramInt2)
  {
    if (paramFloat < 0.0F) {
      return nf(paramFloat, paramInt1, paramInt2);
    }
    return ' ' + nf(paramFloat, paramInt1, paramInt2);
  }
  
  public static String nfs(int paramInt1, int paramInt2)
  {
    if (paramInt1 < 0) {
      return nf(paramInt1, paramInt2);
    }
    return ' ' + nf(paramInt1, paramInt2);
  }
  
  public static String[] nfs(float[] paramArrayOfFloat, int paramInt1, int paramInt2)
  {
    String[] arrayOfString = new String[paramArrayOfFloat.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nfs(paramArrayOfFloat[i], paramInt1, paramInt2);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static String[] nfs(int[] paramArrayOfInt, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfInt.length];
    int i = 0;
    while (i < arrayOfString.length)
    {
      arrayOfString[i] = nfs(paramArrayOfInt[i], paramInt);
      i += 1;
    }
    return arrayOfString;
  }
  
  private float noise_fsc(float paramFloat)
  {
    return 0.5F * (1.0F - this.perlin_cosTable[((int)(this.perlin_PI * paramFloat) % this.perlin_TWOPI)]);
  }
  
  public static final float norm(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return (paramFloat1 - paramFloat2) / (paramFloat3 - paramFloat2);
  }
  
  public static Process open(String[] paramArrayOfString)
  {
    return exec(paramArrayOfString);
  }
  
  public static void open(String paramString)
  {
    open(new String[] { paramString });
  }
  
  public static final boolean parseBoolean(int paramInt)
  {
    return paramInt != 0;
  }
  
  public static final boolean parseBoolean(String paramString)
  {
    return new Boolean(paramString).booleanValue();
  }
  
  public static final boolean[] parseBoolean(byte[] paramArrayOfByte)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfByte.length];
    int i = 0;
    if (i < paramArrayOfByte.length)
    {
      if (paramArrayOfByte[i] != 0) {}
      for (int j = 1;; j = 0)
      {
        arrayOfBoolean[i] = j;
        i += 1;
        break;
      }
    }
    return arrayOfBoolean;
  }
  
  public static final boolean[] parseBoolean(int[] paramArrayOfInt)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfInt.length];
    int i = 0;
    if (i < paramArrayOfInt.length)
    {
      if (paramArrayOfInt[i] != 0) {}
      for (int j = 1;; j = 0)
      {
        arrayOfBoolean[i] = j;
        i += 1;
        break;
      }
    }
    return arrayOfBoolean;
  }
  
  public static final boolean[] parseBoolean(String[] paramArrayOfString)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfString.length];
    int i = 0;
    while (i < paramArrayOfString.length)
    {
      arrayOfBoolean[i] = new Boolean(paramArrayOfString[i]).booleanValue();
      i += 1;
    }
    return arrayOfBoolean;
  }
  
  public static final byte parseByte(char paramChar)
  {
    return (byte)paramChar;
  }
  
  public static final byte parseByte(float paramFloat)
  {
    return (byte)(int)paramFloat;
  }
  
  public static final byte parseByte(int paramInt)
  {
    return (byte)paramInt;
  }
  
  public static final byte parseByte(boolean paramBoolean)
  {
    if (paramBoolean) {
      return 1;
    }
    return 0;
  }
  
  public static final byte[] parseByte(char[] paramArrayOfChar)
  {
    byte[] arrayOfByte = new byte[paramArrayOfChar.length];
    int i = 0;
    while (i < paramArrayOfChar.length)
    {
      arrayOfByte[i] = ((byte)paramArrayOfChar[i]);
      i += 1;
    }
    return arrayOfByte;
  }
  
  public static final byte[] parseByte(float[] paramArrayOfFloat)
  {
    byte[] arrayOfByte = new byte[paramArrayOfFloat.length];
    int i = 0;
    while (i < paramArrayOfFloat.length)
    {
      arrayOfByte[i] = ((byte)(int)paramArrayOfFloat[i]);
      i += 1;
    }
    return arrayOfByte;
  }
  
  public static final byte[] parseByte(int[] paramArrayOfInt)
  {
    byte[] arrayOfByte = new byte[paramArrayOfInt.length];
    int i = 0;
    while (i < paramArrayOfInt.length)
    {
      arrayOfByte[i] = ((byte)paramArrayOfInt[i]);
      i += 1;
    }
    return arrayOfByte;
  }
  
  public static final byte[] parseByte(boolean[] paramArrayOfBoolean)
  {
    byte[] arrayOfByte = new byte[paramArrayOfBoolean.length];
    int j = 0;
    if (j < paramArrayOfBoolean.length)
    {
      if (paramArrayOfBoolean[j] != 0) {}
      for (int i = 1;; i = 0)
      {
        arrayOfByte[j] = i;
        j += 1;
        break;
      }
    }
    return arrayOfByte;
  }
  
  public static final float[] parseByte(byte[] paramArrayOfByte)
  {
    float[] arrayOfFloat = new float[paramArrayOfByte.length];
    int i = 0;
    while (i < paramArrayOfByte.length)
    {
      arrayOfFloat[i] = paramArrayOfByte[i];
      i += 1;
    }
    return arrayOfFloat;
  }
  
  public static final char parseChar(byte paramByte)
  {
    return (char)(paramByte & 0xFF);
  }
  
  public static final char parseChar(int paramInt)
  {
    return (char)paramInt;
  }
  
  public static final char[] parseChar(byte[] paramArrayOfByte)
  {
    char[] arrayOfChar = new char[paramArrayOfByte.length];
    int i = 0;
    while (i < paramArrayOfByte.length)
    {
      arrayOfChar[i] = ((char)(paramArrayOfByte[i] & 0xFF));
      i += 1;
    }
    return arrayOfChar;
  }
  
  public static final char[] parseChar(int[] paramArrayOfInt)
  {
    char[] arrayOfChar = new char[paramArrayOfInt.length];
    int i = 0;
    while (i < paramArrayOfInt.length)
    {
      arrayOfChar[i] = ((char)paramArrayOfInt[i]);
      i += 1;
    }
    return arrayOfChar;
  }
  
  public static final float parseFloat(int paramInt)
  {
    return paramInt;
  }
  
  public static final float parseFloat(String paramString)
  {
    return parseFloat(paramString, NaN.0F);
  }
  
  public static final float parseFloat(String paramString, float paramFloat)
  {
    try
    {
      float f = new Float(paramString).floatValue();
      return f;
    }
    catch (NumberFormatException paramString) {}
    return paramFloat;
  }
  
  public static final float[] parseFloat(int[] paramArrayOfInt)
  {
    float[] arrayOfFloat = new float[paramArrayOfInt.length];
    int i = 0;
    while (i < paramArrayOfInt.length)
    {
      arrayOfFloat[i] = paramArrayOfInt[i];
      i += 1;
    }
    return arrayOfFloat;
  }
  
  public static final float[] parseFloat(String[] paramArrayOfString)
  {
    return parseFloat(paramArrayOfString, NaN.0F);
  }
  
  public static final float[] parseFloat(String[] paramArrayOfString, float paramFloat)
  {
    float[] arrayOfFloat = new float[paramArrayOfString.length];
    int i = 0;
    for (;;)
    {
      if (i < paramArrayOfString.length) {
        try
        {
          arrayOfFloat[i] = new Float(paramArrayOfString[i]).floatValue();
          i += 1;
        }
        catch (NumberFormatException localNumberFormatException)
        {
          for (;;)
          {
            arrayOfFloat[i] = paramFloat;
          }
        }
      }
    }
    return arrayOfFloat;
  }
  
  public static final int parseInt(byte paramByte)
  {
    return paramByte & 0xFF;
  }
  
  public static final int parseInt(char paramChar)
  {
    return paramChar;
  }
  
  public static final int parseInt(float paramFloat)
  {
    return (int)paramFloat;
  }
  
  public static final int parseInt(String paramString)
  {
    return parseInt(paramString, 0);
  }
  
  public static final int parseInt(String paramString, int paramInt)
  {
    try
    {
      int i = paramString.indexOf('.');
      if (i == -1) {
        return Integer.parseInt(paramString);
      }
      i = Integer.parseInt(paramString.substring(0, i));
      return i;
    }
    catch (NumberFormatException paramString) {}
    return paramInt;
  }
  
  public static final int parseInt(boolean paramBoolean)
  {
    if (paramBoolean) {
      return 1;
    }
    return 0;
  }
  
  public static final int[] parseInt(byte[] paramArrayOfByte)
  {
    int[] arrayOfInt = new int[paramArrayOfByte.length];
    int i = 0;
    while (i < paramArrayOfByte.length)
    {
      paramArrayOfByte[i] &= 0xFF;
      i += 1;
    }
    return arrayOfInt;
  }
  
  public static final int[] parseInt(char[] paramArrayOfChar)
  {
    int[] arrayOfInt = new int[paramArrayOfChar.length];
    int i = 0;
    while (i < paramArrayOfChar.length)
    {
      arrayOfInt[i] = paramArrayOfChar[i];
      i += 1;
    }
    return arrayOfInt;
  }
  
  public static int[] parseInt(float[] paramArrayOfFloat)
  {
    int[] arrayOfInt = new int[paramArrayOfFloat.length];
    int i = 0;
    while (i < paramArrayOfFloat.length)
    {
      arrayOfInt[i] = ((int)paramArrayOfFloat[i]);
      i += 1;
    }
    return arrayOfInt;
  }
  
  public static int[] parseInt(String[] paramArrayOfString)
  {
    return parseInt(paramArrayOfString, 0);
  }
  
  public static int[] parseInt(String[] paramArrayOfString, int paramInt)
  {
    int[] arrayOfInt = new int[paramArrayOfString.length];
    int i = 0;
    for (;;)
    {
      if (i < paramArrayOfString.length) {
        try
        {
          arrayOfInt[i] = Integer.parseInt(paramArrayOfString[i]);
          i += 1;
        }
        catch (NumberFormatException localNumberFormatException)
        {
          for (;;)
          {
            arrayOfInt[i] = paramInt;
          }
        }
      }
    }
    return arrayOfInt;
  }
  
  public static final int[] parseInt(boolean[] paramArrayOfBoolean)
  {
    int[] arrayOfInt = new int[paramArrayOfBoolean.length];
    int i = 0;
    if (i < paramArrayOfBoolean.length)
    {
      if (paramArrayOfBoolean[i] != 0) {}
      for (int j = 1;; j = 0)
      {
        arrayOfInt[i] = j;
        i += 1;
        break;
      }
    }
    return arrayOfInt;
  }
  
  public static final float pow(float paramFloat1, float paramFloat2)
  {
    return (float)Math.pow(paramFloat1, paramFloat2);
  }
  
  public static void print(byte paramByte)
  {
    System.out.print(paramByte);
    System.out.flush();
  }
  
  public static void print(char paramChar)
  {
    System.out.print(paramChar);
    System.out.flush();
  }
  
  public static void print(float paramFloat)
  {
    System.out.print(paramFloat);
    System.out.flush();
  }
  
  public static void print(int paramInt)
  {
    System.out.print(paramInt);
    System.out.flush();
  }
  
  public static void print(Object paramObject)
  {
    if (paramObject == null)
    {
      System.out.print("null");
      return;
    }
    System.out.println(paramObject.toString());
  }
  
  public static void print(String paramString)
  {
    System.out.print(paramString);
    System.out.flush();
  }
  
  public static void print(boolean paramBoolean)
  {
    System.out.print(paramBoolean);
    System.out.flush();
  }
  
  public static void println()
  {
    System.out.println();
  }
  
  public static void println(byte paramByte)
  {
    print(paramByte);
    System.out.println();
  }
  
  public static void println(char paramChar)
  {
    print(paramChar);
    System.out.println();
  }
  
  public static void println(float paramFloat)
  {
    print(paramFloat);
    System.out.println();
  }
  
  public static void println(int paramInt)
  {
    print(paramInt);
    System.out.println();
  }
  
  public static void println(Object paramObject)
  {
    int j = 0;
    int k = 0;
    int m = 0;
    int n = 0;
    int i1 = 0;
    int i = 0;
    if (paramObject == null) {
      System.out.println("null");
    }
    for (;;)
    {
      return;
      String str = paramObject.getClass().getName();
      if (str.charAt(0) != '[') {
        break;
      }
      switch (str.charAt(1))
      {
      default: 
        System.out.println(paramObject);
        return;
      case '[': 
        System.out.println(paramObject);
        return;
      case 'L': 
        paramObject = (Object[])paramObject;
        if (i < paramObject.length)
        {
          if ((paramObject[i] instanceof String)) {
            System.out.println("[" + i + "] \"" + paramObject[i] + "\"");
          }
          for (;;)
          {
            i += 1;
            break;
            System.out.println("[" + i + "] " + paramObject[i]);
          }
        }
        break;
      case 'Z': 
        paramObject = (boolean[])paramObject;
        i = j;
        while (i < paramObject.length)
        {
          System.out.println("[" + i + "] " + paramObject[i]);
          i += 1;
        }
      case 'B': 
        paramObject = (byte[])paramObject;
        i = k;
        while (i < paramObject.length)
        {
          System.out.println("[" + i + "] " + paramObject[i]);
          i += 1;
        }
      case 'C': 
        paramObject = (char[])paramObject;
        i = m;
        while (i < paramObject.length)
        {
          System.out.println("[" + i + "] '" + paramObject[i] + "'");
          i += 1;
        }
      case 'I': 
        paramObject = (int[])paramObject;
        i = n;
        while (i < paramObject.length)
        {
          System.out.println("[" + i + "] " + paramObject[i]);
          i += 1;
        }
      case 'F': 
        paramObject = (float[])paramObject;
        i = i1;
        while (i < paramObject.length)
        {
          System.out.println("[" + i + "] " + paramObject[i]);
          i += 1;
        }
      }
    }
    System.out.println(paramObject);
  }
  
  public static void println(String paramString)
  {
    print(paramString);
    System.out.println();
  }
  
  public static void println(boolean paramBoolean)
  {
    print(paramBoolean);
    System.out.println();
  }
  
  public static final float radians(float paramFloat)
  {
    return 0.017453292F * paramFloat;
  }
  
  private void registerNoArgs(String paramString, Object paramObject)
  {
    Object localObject2 = (RegisteredMethods)this.registerMap.get(paramString);
    Object localObject1 = localObject2;
    if (localObject2 == null)
    {
      localObject1 = new RegisteredMethods();
      this.registerMap.put(paramString, localObject1);
    }
    localObject2 = paramObject.getClass();
    try
    {
      ((RegisteredMethods)localObject1).add(paramObject, ((Class)localObject2).getMethod(paramString, new Class[0]));
      return;
    }
    catch (NoSuchMethodException localNoSuchMethodException)
    {
      die("There is no public " + paramString + "() method in the class " + paramObject.getClass().getName());
      return;
    }
    catch (Exception localException)
    {
      die("Could not register " + paramString + " + () for " + paramObject, localException);
    }
  }
  
  private void registerWithArgs(String paramString, Object paramObject, Class<?>[] paramArrayOfClass)
  {
    Object localObject2 = (RegisteredMethods)this.registerMap.get(paramString);
    Object localObject1 = localObject2;
    if (localObject2 == null)
    {
      localObject1 = new RegisteredMethods();
      this.registerMap.put(paramString, localObject1);
    }
    localObject2 = paramObject.getClass();
    try
    {
      ((RegisteredMethods)localObject1).add(paramObject, ((Class)localObject2).getMethod(paramString, paramArrayOfClass));
      return;
    }
    catch (NoSuchMethodException paramArrayOfClass)
    {
      die("There is no public " + paramString + "() method in the class " + paramObject.getClass().getName());
      return;
    }
    catch (Exception paramArrayOfClass)
    {
      die("Could not register " + paramString + " + () for " + paramObject, paramArrayOfClass);
    }
  }
  
  public static Object reverse(Object paramObject)
  {
    Object localObject = paramObject.getClass().getComponentType();
    int j = Array.getLength(paramObject);
    localObject = Array.newInstance((Class)localObject, j);
    int i = 0;
    while (i < j)
    {
      Array.set(localObject, i, Array.get(paramObject, j - 1 - i));
      i += 1;
    }
    return localObject;
  }
  
  public static byte[] reverse(byte[] paramArrayOfByte)
  {
    byte[] arrayOfByte = new byte[paramArrayOfByte.length];
    int j = paramArrayOfByte.length;
    int i = 0;
    while (i < paramArrayOfByte.length)
    {
      arrayOfByte[i] = paramArrayOfByte[(j - 1 - i)];
      i += 1;
    }
    return arrayOfByte;
  }
  
  public static char[] reverse(char[] paramArrayOfChar)
  {
    char[] arrayOfChar = new char[paramArrayOfChar.length];
    int j = paramArrayOfChar.length;
    int i = 0;
    while (i < paramArrayOfChar.length)
    {
      arrayOfChar[i] = paramArrayOfChar[(j - 1 - i)];
      i += 1;
    }
    return arrayOfChar;
  }
  
  public static float[] reverse(float[] paramArrayOfFloat)
  {
    float[] arrayOfFloat = new float[paramArrayOfFloat.length];
    int j = paramArrayOfFloat.length;
    int i = 0;
    while (i < paramArrayOfFloat.length)
    {
      arrayOfFloat[i] = paramArrayOfFloat[(j - 1 - i)];
      i += 1;
    }
    return arrayOfFloat;
  }
  
  public static int[] reverse(int[] paramArrayOfInt)
  {
    int[] arrayOfInt = new int[paramArrayOfInt.length];
    int j = paramArrayOfInt.length;
    int i = 0;
    while (i < paramArrayOfInt.length)
    {
      arrayOfInt[i] = paramArrayOfInt[(j - 1 - i)];
      i += 1;
    }
    return arrayOfInt;
  }
  
  public static String[] reverse(String[] paramArrayOfString)
  {
    String[] arrayOfString = new String[paramArrayOfString.length];
    int j = paramArrayOfString.length;
    int i = 0;
    while (i < paramArrayOfString.length)
    {
      arrayOfString[i] = paramArrayOfString[(j - 1 - i)];
      i += 1;
    }
    return arrayOfString;
  }
  
  public static boolean[] reverse(boolean[] paramArrayOfBoolean)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfBoolean.length];
    int j = paramArrayOfBoolean.length;
    int i = 0;
    while (i < paramArrayOfBoolean.length)
    {
      arrayOfBoolean[i] = paramArrayOfBoolean[(j - 1 - i)];
      i += 1;
    }
    return arrayOfBoolean;
  }
  
  public static final int round(float paramFloat)
  {
    return Math.round(paramFloat);
  }
  
  public static void saveBytes(File paramFile, byte[] paramArrayOfByte)
  {
    for (;;)
    {
      try
      {
        createPath(paramFile.getAbsolutePath());
        Object localObject = new FileOutputStream(paramFile);
        if (paramFile.getName().toLowerCase().endsWith(".gz"))
        {
          localObject = new GZIPOutputStream((OutputStream)localObject);
          saveBytes((OutputStream)localObject, paramArrayOfByte);
          ((OutputStream)localObject).close();
          return;
        }
      }
      catch (IOException paramArrayOfByte)
      {
        System.err.println("error saving bytes to " + paramFile);
        paramArrayOfByte.printStackTrace();
        return;
      }
    }
  }
  
  public static void saveBytes(OutputStream paramOutputStream, byte[] paramArrayOfByte)
  {
    try
    {
      paramOutputStream.write(paramArrayOfByte);
      paramOutputStream.flush();
      return;
    }
    catch (IOException paramOutputStream)
    {
      paramOutputStream.printStackTrace();
    }
  }
  
  public static boolean saveStream(File paramFile, InputStream paramInputStream)
  {
    File localFile2 = null;
    File localFile1 = localFile2;
    Object localObject;
    try
    {
      localObject = paramFile.getParentFile();
      localFile1 = localFile2;
      createPath(paramFile);
      localFile1 = localFile2;
      localFile2 = File.createTempFile(paramFile.getName(), null, (File)localObject);
      localFile1 = localFile2;
      paramInputStream = new BufferedInputStream(paramInputStream, 16384);
      localFile1 = localFile2;
      localObject = new BufferedOutputStream(new FileOutputStream(localFile2));
      localFile1 = localFile2;
      byte[] arrayOfByte = new byte['?'];
      for (;;)
      {
        localFile1 = localFile2;
        int i = paramInputStream.read(arrayOfByte);
        if (i == -1) {
          break;
        }
        localFile1 = localFile2;
        ((BufferedOutputStream)localObject).write(arrayOfByte, 0, i);
      }
      localFile1 = localFile2;
    }
    catch (IOException paramFile)
    {
      if (localFile1 != null) {
        localFile1.delete();
      }
      paramFile.printStackTrace();
      return false;
    }
    ((BufferedOutputStream)localObject).flush();
    localFile1 = localFile2;
    ((BufferedOutputStream)localObject).close();
    localFile1 = localFile2;
    if (paramFile.exists())
    {
      localFile1 = localFile2;
      if (!paramFile.delete())
      {
        localFile1 = localFile2;
        System.err.println("Could not replace " + paramFile.getAbsolutePath() + ".");
      }
    }
    localFile1 = localFile2;
    if (!localFile2.renameTo(paramFile))
    {
      localFile1 = localFile2;
      System.err.println("Could not rename temporary file " + localFile2.getAbsolutePath());
      return false;
    }
    return true;
  }
  
  public static void saveStrings(File paramFile, String[] paramArrayOfString)
  {
    for (;;)
    {
      Object localObject;
      try
      {
        localObject = paramFile.getAbsolutePath();
        createPath((String)localObject);
        localObject = new FileOutputStream((String)localObject);
        if (paramFile.getName().toLowerCase().endsWith(".gz"))
        {
          paramFile = new GZIPOutputStream((OutputStream)localObject);
          saveStrings(paramFile, paramArrayOfString);
          paramFile.close();
          return;
        }
      }
      catch (IOException paramFile)
      {
        paramFile.printStackTrace();
        return;
      }
      paramFile = (File)localObject;
    }
  }
  
  public static void saveStrings(OutputStream paramOutputStream, String[] paramArrayOfString)
  {
    try
    {
      paramOutputStream = new PrintWriter(new OutputStreamWriter(paramOutputStream, "UTF-8"));
      int i = 0;
      while (i < paramArrayOfString.length)
      {
        paramOutputStream.println(paramArrayOfString[i]);
        i += 1;
      }
      paramOutputStream.flush();
      return;
    }
    catch (UnsupportedEncodingException paramOutputStream) {}
  }
  
  public static int second()
  {
    time.setToNow();
    return time.second;
  }
  
  public static Object shorten(Object paramObject)
  {
    return subset(paramObject, 0, Array.getLength(paramObject) - 1);
  }
  
  public static byte[] shorten(byte[] paramArrayOfByte)
  {
    return subset(paramArrayOfByte, 0, paramArrayOfByte.length - 1);
  }
  
  public static char[] shorten(char[] paramArrayOfChar)
  {
    return subset(paramArrayOfChar, 0, paramArrayOfChar.length - 1);
  }
  
  public static float[] shorten(float[] paramArrayOfFloat)
  {
    return subset(paramArrayOfFloat, 0, paramArrayOfFloat.length - 1);
  }
  
  public static int[] shorten(int[] paramArrayOfInt)
  {
    return subset(paramArrayOfInt, 0, paramArrayOfInt.length - 1);
  }
  
  public static String[] shorten(String[] paramArrayOfString)
  {
    return subset(paramArrayOfString, 0, paramArrayOfString.length - 1);
  }
  
  public static boolean[] shorten(boolean[] paramArrayOfBoolean)
  {
    return subset(paramArrayOfBoolean, 0, paramArrayOfBoolean.length - 1);
  }
  
  public static void showDepthWarning(String paramString)
  {
    PGraphics.showDepthWarning(paramString);
  }
  
  public static void showDepthWarningXYZ(String paramString)
  {
    PGraphics.showDepthWarningXYZ(paramString);
  }
  
  public static void showMethodWarning(String paramString)
  {
    PGraphics.showMethodWarning(paramString);
  }
  
  public static void showMissingWarning(String paramString)
  {
    PGraphics.showMissingWarning(paramString);
  }
  
  public static void showVariationWarning(String paramString)
  {
    PGraphics.showVariationWarning(paramString);
  }
  
  public static final float sin(float paramFloat)
  {
    return (float)Math.sin(paramFloat);
  }
  
  public static byte[] sort(byte[] paramArrayOfByte)
  {
    return sort(paramArrayOfByte, paramArrayOfByte.length);
  }
  
  public static byte[] sort(byte[] paramArrayOfByte, int paramInt)
  {
    byte[] arrayOfByte = new byte[paramArrayOfByte.length];
    System.arraycopy(paramArrayOfByte, 0, arrayOfByte, 0, paramArrayOfByte.length);
    Arrays.sort(arrayOfByte, 0, paramInt);
    return arrayOfByte;
  }
  
  public static char[] sort(char[] paramArrayOfChar)
  {
    return sort(paramArrayOfChar, paramArrayOfChar.length);
  }
  
  public static char[] sort(char[] paramArrayOfChar, int paramInt)
  {
    char[] arrayOfChar = new char[paramArrayOfChar.length];
    System.arraycopy(paramArrayOfChar, 0, arrayOfChar, 0, paramArrayOfChar.length);
    Arrays.sort(arrayOfChar, 0, paramInt);
    return arrayOfChar;
  }
  
  public static float[] sort(float[] paramArrayOfFloat)
  {
    return sort(paramArrayOfFloat, paramArrayOfFloat.length);
  }
  
  public static float[] sort(float[] paramArrayOfFloat, int paramInt)
  {
    float[] arrayOfFloat = new float[paramArrayOfFloat.length];
    System.arraycopy(paramArrayOfFloat, 0, arrayOfFloat, 0, paramArrayOfFloat.length);
    Arrays.sort(arrayOfFloat, 0, paramInt);
    return arrayOfFloat;
  }
  
  public static int[] sort(int[] paramArrayOfInt)
  {
    return sort(paramArrayOfInt, paramArrayOfInt.length);
  }
  
  public static int[] sort(int[] paramArrayOfInt, int paramInt)
  {
    int[] arrayOfInt = new int[paramArrayOfInt.length];
    System.arraycopy(paramArrayOfInt, 0, arrayOfInt, 0, paramArrayOfInt.length);
    Arrays.sort(arrayOfInt, 0, paramInt);
    return arrayOfInt;
  }
  
  public static String[] sort(String[] paramArrayOfString)
  {
    return sort(paramArrayOfString, paramArrayOfString.length);
  }
  
  public static String[] sort(String[] paramArrayOfString, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfString.length];
    System.arraycopy(paramArrayOfString, 0, arrayOfString, 0, paramArrayOfString.length);
    Arrays.sort(arrayOfString, 0, paramInt);
    return arrayOfString;
  }
  
  public static final Object splice(Object paramObject1, Object paramObject2, int paramInt)
  {
    int i = Array.getLength(paramObject1);
    if (paramObject2.getClass().getName().charAt(0) == '[')
    {
      int j = Array.getLength(paramObject2);
      arrayOfObject = new Object[i + j];
      System.arraycopy(paramObject1, 0, arrayOfObject, 0, paramInt);
      System.arraycopy(paramObject2, 0, arrayOfObject, paramInt, j);
      System.arraycopy(paramObject1, paramInt, arrayOfObject, j + paramInt, i - paramInt);
      return arrayOfObject;
    }
    Object[] arrayOfObject = new Object[i + 1];
    System.arraycopy(paramObject1, 0, arrayOfObject, 0, paramInt);
    Array.set(arrayOfObject, paramInt, paramObject2);
    System.arraycopy(paramObject1, paramInt, arrayOfObject, paramInt + 1, i - paramInt);
    return arrayOfObject;
  }
  
  public static final byte[] splice(byte[] paramArrayOfByte, byte paramByte, int paramInt)
  {
    byte[] arrayOfByte = new byte[paramArrayOfByte.length + 1];
    System.arraycopy(paramArrayOfByte, 0, arrayOfByte, 0, paramInt);
    arrayOfByte[paramInt] = paramByte;
    System.arraycopy(paramArrayOfByte, paramInt, arrayOfByte, paramInt + 1, paramArrayOfByte.length - paramInt);
    return arrayOfByte;
  }
  
  public static final byte[] splice(byte[] paramArrayOfByte1, byte[] paramArrayOfByte2, int paramInt)
  {
    byte[] arrayOfByte = new byte[paramArrayOfByte1.length + paramArrayOfByte2.length];
    System.arraycopy(paramArrayOfByte1, 0, arrayOfByte, 0, paramInt);
    System.arraycopy(paramArrayOfByte2, 0, arrayOfByte, paramInt, paramArrayOfByte2.length);
    System.arraycopy(paramArrayOfByte1, paramInt, arrayOfByte, paramArrayOfByte2.length + paramInt, paramArrayOfByte1.length - paramInt);
    return arrayOfByte;
  }
  
  public static final char[] splice(char[] paramArrayOfChar, char paramChar, int paramInt)
  {
    char[] arrayOfChar = new char[paramArrayOfChar.length + 1];
    System.arraycopy(paramArrayOfChar, 0, arrayOfChar, 0, paramInt);
    arrayOfChar[paramInt] = paramChar;
    System.arraycopy(paramArrayOfChar, paramInt, arrayOfChar, paramInt + 1, paramArrayOfChar.length - paramInt);
    return arrayOfChar;
  }
  
  public static final char[] splice(char[] paramArrayOfChar1, char[] paramArrayOfChar2, int paramInt)
  {
    char[] arrayOfChar = new char[paramArrayOfChar1.length + paramArrayOfChar2.length];
    System.arraycopy(paramArrayOfChar1, 0, arrayOfChar, 0, paramInt);
    System.arraycopy(paramArrayOfChar2, 0, arrayOfChar, paramInt, paramArrayOfChar2.length);
    System.arraycopy(paramArrayOfChar1, paramInt, arrayOfChar, paramArrayOfChar2.length + paramInt, paramArrayOfChar1.length - paramInt);
    return arrayOfChar;
  }
  
  public static final float[] splice(float[] paramArrayOfFloat, float paramFloat, int paramInt)
  {
    float[] arrayOfFloat = new float[paramArrayOfFloat.length + 1];
    System.arraycopy(paramArrayOfFloat, 0, arrayOfFloat, 0, paramInt);
    arrayOfFloat[paramInt] = paramFloat;
    System.arraycopy(paramArrayOfFloat, paramInt, arrayOfFloat, paramInt + 1, paramArrayOfFloat.length - paramInt);
    return arrayOfFloat;
  }
  
  public static final float[] splice(float[] paramArrayOfFloat1, float[] paramArrayOfFloat2, int paramInt)
  {
    float[] arrayOfFloat = new float[paramArrayOfFloat1.length + paramArrayOfFloat2.length];
    System.arraycopy(paramArrayOfFloat1, 0, arrayOfFloat, 0, paramInt);
    System.arraycopy(paramArrayOfFloat2, 0, arrayOfFloat, paramInt, paramArrayOfFloat2.length);
    System.arraycopy(paramArrayOfFloat1, paramInt, arrayOfFloat, paramArrayOfFloat2.length + paramInt, paramArrayOfFloat1.length - paramInt);
    return arrayOfFloat;
  }
  
  public static final int[] splice(int[] paramArrayOfInt, int paramInt1, int paramInt2)
  {
    int[] arrayOfInt = new int[paramArrayOfInt.length + 1];
    System.arraycopy(paramArrayOfInt, 0, arrayOfInt, 0, paramInt2);
    arrayOfInt[paramInt2] = paramInt1;
    System.arraycopy(paramArrayOfInt, paramInt2, arrayOfInt, paramInt2 + 1, paramArrayOfInt.length - paramInt2);
    return arrayOfInt;
  }
  
  public static final int[] splice(int[] paramArrayOfInt1, int[] paramArrayOfInt2, int paramInt)
  {
    int[] arrayOfInt = new int[paramArrayOfInt1.length + paramArrayOfInt2.length];
    System.arraycopy(paramArrayOfInt1, 0, arrayOfInt, 0, paramInt);
    System.arraycopy(paramArrayOfInt2, 0, arrayOfInt, paramInt, paramArrayOfInt2.length);
    System.arraycopy(paramArrayOfInt1, paramInt, arrayOfInt, paramArrayOfInt2.length + paramInt, paramArrayOfInt1.length - paramInt);
    return arrayOfInt;
  }
  
  public static final String[] splice(String[] paramArrayOfString, String paramString, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfString.length + 1];
    System.arraycopy(paramArrayOfString, 0, arrayOfString, 0, paramInt);
    arrayOfString[paramInt] = paramString;
    System.arraycopy(paramArrayOfString, paramInt, arrayOfString, paramInt + 1, paramArrayOfString.length - paramInt);
    return arrayOfString;
  }
  
  public static final String[] splice(String[] paramArrayOfString1, String[] paramArrayOfString2, int paramInt)
  {
    String[] arrayOfString = new String[paramArrayOfString1.length + paramArrayOfString2.length];
    System.arraycopy(paramArrayOfString1, 0, arrayOfString, 0, paramInt);
    System.arraycopy(paramArrayOfString2, 0, arrayOfString, paramInt, paramArrayOfString2.length);
    System.arraycopy(paramArrayOfString1, paramInt, arrayOfString, paramArrayOfString2.length + paramInt, paramArrayOfString1.length - paramInt);
    return arrayOfString;
  }
  
  public static final boolean[] splice(boolean[] paramArrayOfBoolean, boolean paramBoolean, int paramInt)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfBoolean.length + 1];
    System.arraycopy(paramArrayOfBoolean, 0, arrayOfBoolean, 0, paramInt);
    arrayOfBoolean[paramInt] = paramBoolean;
    System.arraycopy(paramArrayOfBoolean, paramInt, arrayOfBoolean, paramInt + 1, paramArrayOfBoolean.length - paramInt);
    return arrayOfBoolean;
  }
  
  public static final boolean[] splice(boolean[] paramArrayOfBoolean1, boolean[] paramArrayOfBoolean2, int paramInt)
  {
    boolean[] arrayOfBoolean = new boolean[paramArrayOfBoolean1.length + paramArrayOfBoolean2.length];
    System.arraycopy(paramArrayOfBoolean1, 0, arrayOfBoolean, 0, paramInt);
    System.arraycopy(paramArrayOfBoolean2, 0, arrayOfBoolean, paramInt, paramArrayOfBoolean2.length);
    System.arraycopy(paramArrayOfBoolean1, paramInt, arrayOfBoolean, paramArrayOfBoolean2.length + paramInt, paramArrayOfBoolean1.length - paramInt);
    return arrayOfBoolean;
  }
  
  public static String[] split(String paramString, char paramChar)
  {
    int m = 0;
    if (paramString == null) {
      return null;
    }
    char[] arrayOfChar = paramString.toCharArray();
    int i = 0;
    for (int j = 0; i < arrayOfChar.length; j = k)
    {
      k = j;
      if (arrayOfChar[i] == paramChar) {
        k = j + 1;
      }
      i += 1;
    }
    if (j == 0) {
      return new String[] { new String(paramString) };
    }
    paramString = new String[j + 1];
    int k = 0;
    j = 0;
    i = m;
    m = k;
    while (i < arrayOfChar.length)
    {
      int n = m;
      k = j;
      if (arrayOfChar[i] == paramChar)
      {
        paramString[j] = new String(arrayOfChar, m, i - m);
        n = i + 1;
        k = j + 1;
      }
      i += 1;
      m = n;
      j = k;
    }
    paramString[j] = new String(arrayOfChar, m, arrayOfChar.length - m);
    return paramString;
  }
  
  public static String[] split(String paramString1, String paramString2)
  {
    ArrayList localArrayList = new ArrayList();
    int j;
    for (int i = 0;; i = paramString2.length() + j)
    {
      j = paramString1.indexOf(paramString2, i);
      if (j == -1) {
        break;
      }
      localArrayList.add(paramString1.substring(i, j));
    }
    localArrayList.add(paramString1.substring(i));
    paramString1 = new String[localArrayList.size()];
    localArrayList.toArray(paramString1);
    return paramString1;
  }
  
  public static String[] splitTokens(String paramString)
  {
    return splitTokens(paramString, " \t\n\r\f�");
  }
  
  public static String[] splitTokens(String paramString1, String paramString2)
  {
    paramString1 = new StringTokenizer(paramString1, paramString2);
    paramString2 = new String[paramString1.countTokens()];
    int i = 0;
    while (paramString1.hasMoreTokens())
    {
      paramString2[i] = paramString1.nextToken();
      i += 1;
    }
    return paramString2;
  }
  
  public static final float sq(float paramFloat)
  {
    return paramFloat * paramFloat;
  }
  
  public static final float sqrt(float paramFloat)
  {
    return (float)Math.sqrt(paramFloat);
  }
  
  public static final String str(byte paramByte)
  {
    return String.valueOf(paramByte);
  }
  
  public static final String str(char paramChar)
  {
    return String.valueOf(paramChar);
  }
  
  public static final String str(float paramFloat)
  {
    return String.valueOf(paramFloat);
  }
  
  public static final String str(int paramInt)
  {
    return String.valueOf(paramInt);
  }
  
  public static final String str(boolean paramBoolean)
  {
    return String.valueOf(paramBoolean);
  }
  
  public static final String[] str(byte[] paramArrayOfByte)
  {
    String[] arrayOfString = new String[paramArrayOfByte.length];
    int i = 0;
    while (i < paramArrayOfByte.length)
    {
      arrayOfString[i] = String.valueOf(paramArrayOfByte[i]);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static final String[] str(char[] paramArrayOfChar)
  {
    String[] arrayOfString = new String[paramArrayOfChar.length];
    int i = 0;
    while (i < paramArrayOfChar.length)
    {
      arrayOfString[i] = String.valueOf(paramArrayOfChar[i]);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static final String[] str(float[] paramArrayOfFloat)
  {
    String[] arrayOfString = new String[paramArrayOfFloat.length];
    int i = 0;
    while (i < paramArrayOfFloat.length)
    {
      arrayOfString[i] = String.valueOf(paramArrayOfFloat[i]);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static final String[] str(int[] paramArrayOfInt)
  {
    String[] arrayOfString = new String[paramArrayOfInt.length];
    int i = 0;
    while (i < paramArrayOfInt.length)
    {
      arrayOfString[i] = String.valueOf(paramArrayOfInt[i]);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static final String[] str(boolean[] paramArrayOfBoolean)
  {
    String[] arrayOfString = new String[paramArrayOfBoolean.length];
    int i = 0;
    while (i < paramArrayOfBoolean.length)
    {
      arrayOfString[i] = String.valueOf(paramArrayOfBoolean[i]);
      i += 1;
    }
    return arrayOfString;
  }
  
  public static Object subset(Object paramObject, int paramInt)
  {
    return subset(paramObject, paramInt, Array.getLength(paramObject) - paramInt);
  }
  
  public static Object subset(Object paramObject, int paramInt1, int paramInt2)
  {
    Object localObject = Array.newInstance(paramObject.getClass().getComponentType(), paramInt2);
    System.arraycopy(paramObject, paramInt1, localObject, 0, paramInt2);
    return localObject;
  }
  
  public static byte[] subset(byte[] paramArrayOfByte, int paramInt)
  {
    return subset(paramArrayOfByte, paramInt, paramArrayOfByte.length - paramInt);
  }
  
  public static byte[] subset(byte[] paramArrayOfByte, int paramInt1, int paramInt2)
  {
    byte[] arrayOfByte = new byte[paramInt2];
    System.arraycopy(paramArrayOfByte, paramInt1, arrayOfByte, 0, paramInt2);
    return arrayOfByte;
  }
  
  public static char[] subset(char[] paramArrayOfChar, int paramInt)
  {
    return subset(paramArrayOfChar, paramInt, paramArrayOfChar.length - paramInt);
  }
  
  public static char[] subset(char[] paramArrayOfChar, int paramInt1, int paramInt2)
  {
    char[] arrayOfChar = new char[paramInt2];
    System.arraycopy(paramArrayOfChar, paramInt1, arrayOfChar, 0, paramInt2);
    return arrayOfChar;
  }
  
  public static float[] subset(float[] paramArrayOfFloat, int paramInt)
  {
    return subset(paramArrayOfFloat, paramInt, paramArrayOfFloat.length - paramInt);
  }
  
  public static float[] subset(float[] paramArrayOfFloat, int paramInt1, int paramInt2)
  {
    float[] arrayOfFloat = new float[paramInt2];
    System.arraycopy(paramArrayOfFloat, paramInt1, arrayOfFloat, 0, paramInt2);
    return arrayOfFloat;
  }
  
  public static int[] subset(int[] paramArrayOfInt, int paramInt)
  {
    return subset(paramArrayOfInt, paramInt, paramArrayOfInt.length - paramInt);
  }
  
  public static int[] subset(int[] paramArrayOfInt, int paramInt1, int paramInt2)
  {
    int[] arrayOfInt = new int[paramInt2];
    System.arraycopy(paramArrayOfInt, paramInt1, arrayOfInt, 0, paramInt2);
    return arrayOfInt;
  }
  
  public static String[] subset(String[] paramArrayOfString, int paramInt)
  {
    return subset(paramArrayOfString, paramInt, paramArrayOfString.length - paramInt);
  }
  
  public static String[] subset(String[] paramArrayOfString, int paramInt1, int paramInt2)
  {
    String[] arrayOfString = new String[paramInt2];
    System.arraycopy(paramArrayOfString, paramInt1, arrayOfString, 0, paramInt2);
    return arrayOfString;
  }
  
  public static boolean[] subset(boolean[] paramArrayOfBoolean, int paramInt)
  {
    return subset(paramArrayOfBoolean, paramInt, paramArrayOfBoolean.length - paramInt);
  }
  
  public static boolean[] subset(boolean[] paramArrayOfBoolean, int paramInt1, int paramInt2)
  {
    boolean[] arrayOfBoolean = new boolean[paramInt2];
    System.arraycopy(paramArrayOfBoolean, paramInt1, arrayOfBoolean, 0, paramInt2);
    return arrayOfBoolean;
  }
  
  public static final float tan(float paramFloat)
  {
    return (float)Math.tan(paramFloat);
  }
  
  private void tellPDE(String paramString)
  {
    Log.i(getComponentName().getPackageName(), "PROCESSING " + paramString);
  }
  
  public static String trim(String paramString)
  {
    return paramString.replace('�', ' ').trim();
  }
  
  public static String[] trim(String[] paramArrayOfString)
  {
    String[] arrayOfString = new String[paramArrayOfString.length];
    int i = 0;
    while (i < paramArrayOfString.length)
    {
      if (paramArrayOfString[i] != null) {
        arrayOfString[i] = paramArrayOfString[i].replace('�', ' ').trim();
      }
      i += 1;
    }
    return arrayOfString;
  }
  
  public static final int unbinary(String paramString)
  {
    return Integer.parseInt(paramString, 2);
  }
  
  public static final int unhex(String paramString)
  {
    return (int)Long.parseLong(paramString, 16);
  }
  
  public static String urlDecode(String paramString)
  {
    try
    {
      paramString = URLDecoder.decode(paramString, "UTF-8");
      return paramString;
    }
    catch (UnsupportedEncodingException paramString) {}
    return null;
  }
  
  public static String urlEncode(String paramString)
  {
    try
    {
      paramString = URLEncoder.encode(paramString, "UTF-8");
      return paramString;
    }
    catch (UnsupportedEncodingException paramString) {}
    return null;
  }
  
  public static int year()
  {
    time.setToNow();
    return time.year;
  }
  
  public final float alpha(int paramInt)
  {
    return this.g.alpha(paramInt);
  }
  
  public void ambient(float paramFloat)
  {
    this.g.ambient(paramFloat);
  }
  
  public void ambient(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.ambient(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void ambient(int paramInt)
  {
    this.g.ambient(paramInt);
  }
  
  public void ambientLight(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.ambientLight(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void ambientLight(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.ambientLight(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public void applyMatrix(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.applyMatrix(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public void applyMatrix(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8, float paramFloat9, float paramFloat10, float paramFloat11, float paramFloat12, float paramFloat13, float paramFloat14, float paramFloat15, float paramFloat16)
  {
    this.g.applyMatrix(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8, paramFloat9, paramFloat10, paramFloat11, paramFloat12, paramFloat13, paramFloat14, paramFloat15, paramFloat16);
  }
  
  public void applyMatrix(PMatrix2D paramPMatrix2D)
  {
    this.g.applyMatrix(paramPMatrix2D);
  }
  
  public void applyMatrix(PMatrix3D paramPMatrix3D)
  {
    this.g.applyMatrix(paramPMatrix3D);
  }
  
  public void applyMatrix(PMatrix paramPMatrix)
  {
    this.g.applyMatrix(paramPMatrix);
  }
  
  public void arc(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.arc(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public void arc(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, int paramInt)
  {
    this.g.arc(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramInt);
  }
  
  public void background(float paramFloat)
  {
    this.g.background(paramFloat);
  }
  
  public void background(float paramFloat1, float paramFloat2)
  {
    this.g.background(paramFloat1, paramFloat2);
  }
  
  public void background(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.background(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void background(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.background(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void background(int paramInt)
  {
    this.g.background(paramInt);
  }
  
  public void background(int paramInt, float paramFloat)
  {
    this.g.background(paramInt, paramFloat);
  }
  
  public void background(PImage paramPImage)
  {
    this.g.background(paramPImage);
  }
  
  public void beginCamera()
  {
    this.g.beginCamera();
  }
  
  public void beginContour()
  {
    this.g.beginContour();
  }
  
  public PGL beginPGL()
  {
    return this.g.beginPGL();
  }
  
  public void beginShape()
  {
    this.g.beginShape();
  }
  
  public void beginShape(int paramInt)
  {
    this.g.beginShape(paramInt);
  }
  
  public void bezier(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8)
  {
    this.g.bezier(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8);
  }
  
  public void bezier(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8, float paramFloat9, float paramFloat10, float paramFloat11, float paramFloat12)
  {
    this.g.bezier(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8, paramFloat9, paramFloat10, paramFloat11, paramFloat12);
  }
  
  public void bezierDetail(int paramInt)
  {
    this.g.bezierDetail(paramInt);
  }
  
  public float bezierPoint(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    return this.g.bezierPoint(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5);
  }
  
  public float bezierTangent(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    return this.g.bezierTangent(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5);
  }
  
  public void bezierVertex(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.bezierVertex(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public void bezierVertex(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8, float paramFloat9)
  {
    this.g.bezierVertex(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8, paramFloat9);
  }
  
  public void blend(int paramInt1, int paramInt2, int paramInt3, int paramInt4, int paramInt5, int paramInt6, int paramInt7, int paramInt8, int paramInt9)
  {
    this.g.blend(paramInt1, paramInt2, paramInt3, paramInt4, paramInt5, paramInt6, paramInt7, paramInt8, paramInt9);
  }
  
  public void blend(PImage paramPImage, int paramInt1, int paramInt2, int paramInt3, int paramInt4, int paramInt5, int paramInt6, int paramInt7, int paramInt8, int paramInt9)
  {
    this.g.blend(paramPImage, paramInt1, paramInt2, paramInt3, paramInt4, paramInt5, paramInt6, paramInt7, paramInt8, paramInt9);
  }
  
  public void blendMode(int paramInt)
  {
    this.g.blendMode(paramInt);
  }
  
  public final float blue(int paramInt)
  {
    return this.g.blue(paramInt);
  }
  
  public void box(float paramFloat)
  {
    this.g.box(paramFloat);
  }
  
  public void box(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.box(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void breakShape()
  {
    this.g.breakShape();
  }
  
  public final float brightness(int paramInt)
  {
    return this.g.brightness(paramInt);
  }
  
  public void camera()
  {
    this.g.camera();
  }
  
  public void camera(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8, float paramFloat9)
  {
    this.g.camera(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8, paramFloat9);
  }
  
  public boolean canDraw()
  {
    return (this.g != null) && (this.surfaceReady) && (!this.paused) && ((this.looping) || (this.redraw));
  }
  
  public void clear()
  {
    this.g.clear();
  }
  
  public void clip(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.clip(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public final int color(float paramFloat)
  {
    int i = 255;
    int j;
    if (this.g == null)
    {
      j = (int)paramFloat;
      if (j <= 255) {}
    }
    for (;;)
    {
      return i | 0xFF000000 | i << 16 | i << 8;
      if (j < 0)
      {
        i = 0;
        continue;
        return this.g.color(paramFloat);
      }
      else
      {
        i = j;
      }
    }
  }
  
  public final int color(float paramFloat1, float paramFloat2)
  {
    if (this.g == null)
    {
      int j = (int)paramFloat1;
      int k = (int)paramFloat2;
      int i;
      if (j > 255)
      {
        i = 255;
        if (k <= 255) {
          break label64;
        }
      }
      for (;;)
      {
        return i | 0xFF000000 | i << 16 | i << 8;
        i = j;
        if (j >= 0) {
          break;
        }
        i = 0;
        break;
        label64:
        if (k >= 0) {}
      }
    }
    return this.g.color(paramFloat1, paramFloat2);
  }
  
  public final int color(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    if (this.g == null)
    {
      float f;
      if (paramFloat1 > 255.0F)
      {
        f = 255.0F;
        if (paramFloat2 <= 255.0F) {
          break label79;
        }
        paramFloat1 = 255.0F;
        label32:
        if (paramFloat3 <= 255.0F) {
          break label92;
        }
        paramFloat2 = 255.0F;
      }
      for (;;)
      {
        return 0xFF000000 | (int)f << 16 | (int)paramFloat1 << 8 | (int)paramFloat2;
        f = paramFloat1;
        if (paramFloat1 >= 0.0F) {
          break;
        }
        f = 0.0F;
        break;
        label79:
        paramFloat1 = paramFloat2;
        if (paramFloat2 >= 0.0F) {
          break label32;
        }
        paramFloat1 = 0.0F;
        break label32;
        label92:
        paramFloat2 = paramFloat3;
        if (paramFloat3 < 0.0F) {
          paramFloat2 = 0.0F;
        }
      }
    }
    return this.g.color(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public final int color(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    if (this.g == null)
    {
      float f;
      if (paramFloat4 > 255.0F)
      {
        f = 255.0F;
        if (paramFloat1 <= 255.0F) {
          break label98;
        }
        paramFloat4 = 255.0F;
        label34:
        if (paramFloat2 <= 255.0F) {
          break label113;
        }
        paramFloat1 = 255.0F;
        label46:
        if (paramFloat3 <= 255.0F) {
          break label126;
        }
        paramFloat2 = 255.0F;
      }
      for (;;)
      {
        return (int)f << 24 | (int)paramFloat4 << 16 | (int)paramFloat1 << 8 | (int)paramFloat2;
        f = paramFloat4;
        if (paramFloat4 >= 0.0F) {
          break;
        }
        f = 0.0F;
        break;
        label98:
        paramFloat4 = paramFloat1;
        if (paramFloat1 >= 0.0F) {
          break label34;
        }
        paramFloat4 = 0.0F;
        break label34;
        label113:
        paramFloat1 = paramFloat2;
        if (paramFloat2 >= 0.0F) {
          break label46;
        }
        paramFloat1 = 0.0F;
        break label46;
        label126:
        paramFloat2 = paramFloat3;
        if (paramFloat3 < 0.0F) {
          paramFloat2 = 0.0F;
        }
      }
    }
    return this.g.color(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public final int color(int paramInt)
  {
    if (this.g == null)
    {
      int i;
      if (paramInt > 255) {
        i = 255;
      }
      for (;;)
      {
        return 0xFF000000 | i << 16 | i << 8 | i;
        i = paramInt;
        if (paramInt < 0) {
          i = 0;
        }
      }
    }
    return this.g.color(paramInt);
  }
  
  public final int color(int paramInt1, int paramInt2)
  {
    if (this.g == null)
    {
      int i;
      if (paramInt2 > 255) {
        i = 255;
      }
      while (paramInt1 > 255)
      {
        return i << 24 | 0xFFFFFF & paramInt1;
        i = paramInt2;
        if (paramInt2 < 0) {
          i = 0;
        }
      }
      return i << 24 | paramInt1 << 16 | paramInt1 << 8 | paramInt1;
    }
    return this.g.color(paramInt1, paramInt2);
  }
  
  public final int color(int paramInt1, int paramInt2, int paramInt3)
  {
    if (this.g == null)
    {
      int i;
      if (paramInt1 > 255)
      {
        i = 255;
        if (paramInt2 <= 255) {
          break label71;
        }
        paramInt1 = 255;
        label30:
        if (paramInt3 <= 255) {
          break label82;
        }
        paramInt2 = 255;
      }
      for (;;)
      {
        return 0xFF000000 | i << 16 | paramInt1 << 8 | paramInt2;
        i = paramInt1;
        if (paramInt1 >= 0) {
          break;
        }
        i = 0;
        break;
        label71:
        paramInt1 = paramInt2;
        if (paramInt2 >= 0) {
          break label30;
        }
        paramInt1 = 0;
        break label30;
        label82:
        paramInt2 = paramInt3;
        if (paramInt3 < 0) {
          paramInt2 = 0;
        }
      }
    }
    return this.g.color(paramInt1, paramInt2, paramInt3);
  }
  
  public final int color(int paramInt1, int paramInt2, int paramInt3, int paramInt4)
  {
    if (this.g == null)
    {
      int i;
      if (paramInt4 > 255)
      {
        i = 255;
        if (paramInt1 <= 255) {
          break label88;
        }
        paramInt4 = 255;
        label32:
        if (paramInt2 <= 255) {
          break label101;
        }
        paramInt1 = 255;
        label43:
        if (paramInt3 <= 255) {
          break label112;
        }
        paramInt2 = 255;
      }
      for (;;)
      {
        return i << 24 | paramInt4 << 16 | paramInt1 << 8 | paramInt2;
        i = paramInt4;
        if (paramInt4 >= 0) {
          break;
        }
        i = 0;
        break;
        label88:
        paramInt4 = paramInt1;
        if (paramInt1 >= 0) {
          break label32;
        }
        paramInt4 = 0;
        break label32;
        label101:
        paramInt1 = paramInt2;
        if (paramInt2 >= 0) {
          break label43;
        }
        paramInt1 = 0;
        break label43;
        label112:
        paramInt2 = paramInt3;
        if (paramInt3 < 0) {
          paramInt2 = 0;
        }
      }
    }
    return this.g.color(paramInt1, paramInt2, paramInt3, paramInt4);
  }
  
  public void colorMode(int paramInt)
  {
    this.g.colorMode(paramInt);
  }
  
  public void colorMode(int paramInt, float paramFloat)
  {
    this.g.colorMode(paramInt, paramFloat);
  }
  
  public void colorMode(int paramInt, float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.colorMode(paramInt, paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void colorMode(int paramInt, float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.colorMode(paramInt, paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void copy(int paramInt1, int paramInt2, int paramInt3, int paramInt4, int paramInt5, int paramInt6, int paramInt7, int paramInt8)
  {
    this.g.copy(paramInt1, paramInt2, paramInt3, paramInt4, paramInt5, paramInt6, paramInt7, paramInt8);
  }
  
  public void copy(PImage paramPImage, int paramInt1, int paramInt2, int paramInt3, int paramInt4, int paramInt5, int paramInt6, int paramInt7, int paramInt8)
  {
    this.g.copy(paramPImage, paramInt1, paramInt2, paramInt3, paramInt4, paramInt5, paramInt6, paramInt7, paramInt8);
  }
  
  protected PFont createDefaultFont(float paramFloat)
  {
    return createFont("SansSerif", paramFloat, true, null);
  }
  
  public PFont createFont(String paramString, float paramFloat)
  {
    return createFont(paramString, paramFloat, true, null);
  }
  
  public PFont createFont(String paramString, float paramFloat, boolean paramBoolean)
  {
    return createFont(paramString, paramFloat, paramBoolean, null);
  }
  
  public PFont createFont(String paramString, float paramFloat, boolean paramBoolean, char[] paramArrayOfChar)
  {
    String str = paramString.toLowerCase();
    if ((str.endsWith(".otf")) || (str.endsWith(".ttf"))) {}
    for (paramString = Typeface.createFromAsset(getBaseContext().getAssets(), paramString);; paramString = (Typeface)PFont.findNative(paramString)) {
      return new PFont(paramString, round(paramFloat), paramBoolean, paramArrayOfChar);
    }
  }
  
  public PGraphics createGraphics(int paramInt1, int paramInt2)
  {
    return createGraphics(paramInt1, paramInt2, "processing.core.PGraphicsAndroid2D");
  }
  
  public PGraphics createGraphics(int paramInt1, int paramInt2, String paramString)
  {
    Object localObject1 = null;
    if (paramString.equals("processing.core.PGraphicsAndroid2D")) {
      paramString = new PGraphicsAndroid2D();
    }
    for (;;)
    {
      paramString.setParent(this);
      paramString.setPrimary(false);
      paramString.setSize(paramInt1, paramInt2);
      return paramString;
      if (paramString.equals("processing.opengl.PGraphics2D"))
      {
        if (!this.g.isGL()) {
          throw new RuntimeException("createGraphics() with P2D requires size() to use P2D or P3D");
        }
        paramString = new PGraphics2D();
        continue;
      }
      if (paramString.equals("processing.opengl.PGraphics3D"))
      {
        if (!this.g.isGL()) {
          throw new RuntimeException("createGraphics() with P3D or OPENGL requires size() to use P2D or P3D");
        }
        paramString = new PGraphics3D();
        continue;
      }
      try
      {
        localObject2 = getClass().getClassLoader().loadClass(paramString);
        paramString = (String)localObject1;
        if (localObject2 == null) {
          continue;
        }
      }
      catch (ClassNotFoundException paramString)
      {
        try
        {
          localObject2 = ((Class)localObject2).getConstructor(new Class[0]);
          paramString = (String)localObject1;
          if (localObject2 == null) {
            continue;
          }
        }
        catch (NoSuchMethodException paramString)
        {
          Object localObject2;
          throw new RuntimeException("Missing renderer constructor");
        }
        try
        {
          paramString = (PGraphics)((Constructor)localObject2).newInstance(new Object[0]);
        }
        catch (InvocationTargetException paramString)
        {
          paramString.printStackTrace();
          throw new RuntimeException(paramString.getMessage());
        }
        catch (IllegalAccessException paramString)
        {
          paramString.printStackTrace();
          throw new RuntimeException(paramString.getMessage());
        }
        catch (InstantiationException paramString)
        {
          paramString.printStackTrace();
          throw new RuntimeException(paramString.getMessage());
        }
        paramString = paramString;
        throw new RuntimeException("Missing renderer class");
      }
    }
  }
  
  public PImage createImage(int paramInt1, int paramInt2, int paramInt3)
  {
    PImage localPImage = new PImage(paramInt1, paramInt2, paramInt3);
    localPImage.parent = this;
    return localPImage;
  }
  
  public InputStream createInput(String paramString)
  {
    InputStream localInputStream = createInputRaw(paramString);
    if ((localInputStream != null) && (paramString.toLowerCase().endsWith(".gz"))) {
      try
      {
        paramString = new GZIPInputStream(localInputStream);
        return paramString;
      }
      catch (IOException paramString)
      {
        paramString.printStackTrace();
        return null;
      }
    }
    return localInputStream;
  }
  
  public InputStream createInputRaw(String paramString)
  {
    if (paramString == null) {}
    for (;;)
    {
      return null;
      if (paramString.length() == 0) {
        continue;
      }
      if (paramString.indexOf(":") != -1) {}
      try
      {
        Object localObject1 = new HttpGet(URI.create(paramString));
        localObject1 = new DefaultHttpClient().execute((HttpUriRequest)localObject1).getEntity().getContent();
        return (InputStream)localObject1;
      }
      catch (IOException paramString)
      {
        paramString.printStackTrace();
        return null;
      }
      catch (FileNotFoundException localFileNotFoundException1)
      {
        Object localObject2 = getAssets();
        try
        {
          localObject2 = ((AssetManager)localObject2).open(paramString);
          if (localObject2 != null) {
            return (InputStream)localObject2;
          }
        }
        catch (IOException localIOException)
        {
          Object localObject3 = new File(paramString);
          if (((File)localObject3).exists()) {
            try
            {
              localObject3 = new FileInputStream((File)localObject3);
              if (localObject3 != null) {
                return (InputStream)localObject3;
              }
            }
            catch (FileNotFoundException localFileNotFoundException2) {}
          }
          Object localObject4 = new File(sketchPath(paramString));
          if (((File)localObject4).exists()) {
            try
            {
              localObject4 = new FileInputStream((File)localObject4);
              if (localObject4 != null) {
                return (InputStream)localObject4;
              }
            }
            catch (FileNotFoundException localFileNotFoundException3) {}
          }
          Context localContext = getApplicationContext();
          try
          {
            paramString = localContext.openFileInput(paramString);
            if (paramString == null) {
              continue;
            }
            return paramString;
          }
          catch (FileNotFoundException paramString)
          {
            return null;
          }
        }
      }
      catch (MalformedURLException localMalformedURLException)
      {
        for (;;) {}
      }
    }
  }
  
  public OutputStream createOutput(String paramString)
  {
    try
    {
      File localFile2 = new File(paramString);
      File localFile1 = localFile2;
      if (!localFile2.isAbsolute()) {
        localFile1 = new File(sketchPath(paramString));
      }
      paramString = new FileOutputStream(localFile1);
      if (localFile1.getName().toLowerCase().endsWith(".gz"))
      {
        paramString = new GZIPOutputStream(paramString);
        return paramString;
      }
      return paramString;
    }
    catch (IOException paramString)
    {
      paramString.printStackTrace();
    }
    return null;
  }
  
  public BufferedReader createReader(String paramString)
  {
    try
    {
      Object localObject = createInput(paramString);
      if (localObject == null)
      {
        System.err.println(paramString + " does not exist or could not be read");
        return null;
      }
      localObject = createReader((InputStream)localObject);
      return (BufferedReader)localObject;
    }
    catch (Exception localException)
    {
      if (paramString == null)
      {
        System.err.println("Filename passed to reader() was null");
        return null;
      }
      System.err.println("Couldn't create a reader for " + paramString);
    }
    return null;
  }
  
  public PShape createShape()
  {
    return this.g.createShape();
  }
  
  public PShape createShape(int paramInt)
  {
    return this.g.createShape(paramInt);
  }
  
  public PShape createShape(int paramInt, float... paramVarArgs)
  {
    return this.g.createShape(paramInt, paramVarArgs);
  }
  
  public PShape createShape(PShape paramPShape)
  {
    return this.g.createShape(paramPShape);
  }
  
  public Table createTable()
  {
    return new Table();
  }
  
  public PrintWriter createWriter(String paramString)
  {
    return createWriter(saveFile(paramString));
  }
  
  public XML createXML(String paramString)
  {
    try
    {
      paramString = new XML(paramString);
      return paramString;
    }
    catch (Exception paramString)
    {
      paramString.printStackTrace();
    }
    return null;
  }
  
  public void curve(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8)
  {
    this.g.curve(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8);
  }
  
  public void curve(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8, float paramFloat9, float paramFloat10, float paramFloat11, float paramFloat12)
  {
    this.g.curve(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8, paramFloat9, paramFloat10, paramFloat11, paramFloat12);
  }
  
  public void curveDetail(int paramInt)
  {
    this.g.curveDetail(paramInt);
  }
  
  public float curvePoint(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    return this.g.curvePoint(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5);
  }
  
  public float curveTangent(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    return this.g.curveTangent(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5);
  }
  
  public void curveTightness(float paramFloat)
  {
    this.g.curveTightness(paramFloat);
  }
  
  public void curveVertex(float paramFloat1, float paramFloat2)
  {
    this.g.curveVertex(paramFloat1, paramFloat2);
  }
  
  public void curveVertex(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.curveVertex(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public File dataFile(String paramString)
  {
    return new File(dataPath(paramString));
  }
  
  public String dataPath(String paramString)
  {
    if (new File(paramString).isAbsolute()) {
      return paramString;
    }
    return this.sketchPath + File.separator + "data" + File.separator + paramString;
  }
  
  public void delay(int paramInt)
  {
    long l = paramInt;
    try
    {
      Thread.sleep(l);
      return;
    }
    catch (InterruptedException localInterruptedException) {}
  }
  
  protected void dequeueEvents()
  {
    while (this.eventQueue.available())
    {
      Event localEvent = this.eventQueue.remove();
      switch (localEvent.getFlavor())
      {
      default: 
        break;
      case 1: 
        handleKeyEvent((processing.event.KeyEvent)localEvent);
        break;
      case 2: 
        handleMouseEvent((MouseEvent)localEvent);
      }
    }
  }
  
  public void destroy()
  {
    exit();
  }
  
  public void die(String paramString)
  {
    stop();
    throw new RuntimeException(paramString);
  }
  
  public void die(String paramString, Exception paramException)
  {
    if (paramException != null) {
      paramException.printStackTrace();
    }
    die(paramString);
  }
  
  public void directionalLight(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.directionalLight(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public boolean displayable()
  {
    return this.g.displayable();
  }
  
  public final void dispose()
  {
    this.finished = true;
    if (this.thread == null) {
      return;
    }
    this.thread = null;
    if (this.g != null) {
      this.g.dispose();
    }
    handleMethods("dispose");
  }
  
  public void draw()
  {
    this.finished = true;
  }
  
  public void edge(boolean paramBoolean)
  {
    this.g.edge(paramBoolean);
  }
  
  public void ellipse(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.ellipse(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void ellipseMode(int paramInt)
  {
    this.g.ellipseMode(paramInt);
  }
  
  public void emissive(float paramFloat)
  {
    this.g.emissive(paramFloat);
  }
  
  public void emissive(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.emissive(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void emissive(int paramInt)
  {
    this.g.emissive(paramInt);
  }
  
  public void endCamera()
  {
    this.g.endCamera();
  }
  
  public void endContour()
  {
    this.g.endContour();
  }
  
  public void endPGL()
  {
    this.g.endPGL();
  }
  
  public void endShape()
  {
    this.g.endShape();
  }
  
  public void endShape(int paramInt)
  {
    this.g.endShape(paramInt);
  }
  
  public void exit()
  {
    if (this.thread == null) {
      exit2();
    }
    do
    {
      return;
      if (this.looping)
      {
        this.finished = true;
        this.exitCalled = true;
        return;
      }
    } while (this.looping);
    dispose();
    exit2();
  }
  
  void exit2()
  {
    try
    {
      System.exit(0);
      return;
    }
    catch (SecurityException localSecurityException) {}
  }
  
  public void fill(float paramFloat)
  {
    this.g.fill(paramFloat);
  }
  
  public void fill(float paramFloat1, float paramFloat2)
  {
    this.g.fill(paramFloat1, paramFloat2);
  }
  
  public void fill(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.fill(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void fill(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.fill(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void fill(int paramInt)
  {
    this.g.fill(paramInt);
  }
  
  public void fill(int paramInt, float paramFloat)
  {
    this.g.fill(paramInt, paramFloat);
  }
  
  public void filter(int paramInt)
  {
    this.g.filter(paramInt);
  }
  
  public void filter(int paramInt, float paramFloat)
  {
    this.g.filter(paramInt, paramFloat);
  }
  
  public void filter(PShader paramPShader)
  {
    this.g.filter(paramPShader);
  }
  
  public void flush()
  {
    this.g.flush();
  }
  
  public void focusGained() {}
  
  public void focusLost() {}
  
  public void frameRate(float paramFloat)
  {
    this.frameRateTarget = paramFloat;
    this.frameRatePeriod = ((1.0E9D / this.frameRateTarget));
    this.g.setFrameRate(paramFloat);
  }
  
  public void frustum(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.frustum(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public int get(int paramInt1, int paramInt2)
  {
    return this.g.get(paramInt1, paramInt2);
  }
  
  public PImage get()
  {
    return this.g.get();
  }
  
  public PImage get(int paramInt1, int paramInt2, int paramInt3, int paramInt4)
  {
    return this.g.get(paramInt1, paramInt2, paramInt3, paramInt4);
  }
  
  public Object getCache(PImage paramPImage)
  {
    return this.g.getCache(paramPImage);
  }
  
  public PMatrix2D getMatrix(PMatrix2D paramPMatrix2D)
  {
    return this.g.getMatrix(paramPMatrix2D);
  }
  
  public PMatrix3D getMatrix(PMatrix3D paramPMatrix3D)
  {
    return this.g.getMatrix(paramPMatrix3D);
  }
  
  public PMatrix getMatrix()
  {
    return this.g.getMatrix();
  }
  
  public Object getNative()
  {
    return this.g.getNative();
  }
  
  public PShader getShader(int paramInt)
  {
    return this.g.getShader(paramInt);
  }
  
  public SurfaceHolder getSurfaceHolder()
  {
    return this.surfaceView.getHolder();
  }
  
  public SurfaceView getSurfaceView()
  {
    return this.surfaceView;
  }
  
  public final float green(int paramInt)
  {
    return this.g.green(paramInt);
  }
  
  public void handleDraw()
  {
    if (this.surfaceChanged)
    {
      int i = this.surfaceView.getWidth();
      int j = this.surfaceView.getHeight();
      if ((i != this.width) || (j != this.height))
      {
        this.width = i;
        this.height = j;
        this.g.setSize(this.width, this.height);
      }
      this.surfaceChanged = false;
      this.surfaceReady = true;
    }
    long l;
    if (canDraw())
    {
      this.g.beginDraw();
      l = System.nanoTime();
      if (this.frameCount != 0) {
        break label140;
      }
    }
    for (;;)
    {
      label140:
      try
      {
        setup();
        this.g.endDraw();
        if (this.frameCount != 0) {
          handleMethods("post");
        }
        this.frameRateLastNanos = l;
        this.frameCount += 1;
        return;
      }
      catch (RendererChangeException localRendererChangeException) {}
      this.frameRate = ((float)(1000000.0D / ((l - this.frameRateLastNanos) / 1000000.0D)) / 1000.0F * 0.1F + this.frameRate * 0.9F);
      if (this.frameCount != 0) {
        handleMethods("pre");
      }
      this.pmouseX = this.dmouseX;
      this.pmouseY = this.dmouseY;
      draw();
      this.dmouseX = this.mouseX;
      this.dmouseY = this.mouseY;
      dequeueEvents();
      handleMethods("draw");
      this.redraw = false;
    }
  }
  
  protected void handleKeyEvent(processing.event.KeyEvent paramKeyEvent)
  {
    this.key = paramKeyEvent.getKey();
    this.keyCode = paramKeyEvent.getKeyCode();
    switch (paramKeyEvent.getAction())
    {
    }
    for (;;)
    {
      handleMethods("keyEvent", new Object[] { paramKeyEvent });
      return;
      this.keyPressed = true;
      keyPressed(paramKeyEvent);
      continue;
      this.keyPressed = false;
      keyReleased(paramKeyEvent);
    }
  }
  
  protected void handleMethods(String paramString)
  {
    paramString = (RegisteredMethods)this.registerMap.get(paramString);
    if (paramString != null) {
      paramString.handle();
    }
  }
  
  protected void handleMethods(String paramString, Object[] paramArrayOfObject)
  {
    paramString = (RegisteredMethods)this.registerMap.get(paramString);
    if (paramString != null) {
      paramString.handle(paramArrayOfObject);
    }
  }
  
  protected void handleMouseEvent(MouseEvent paramMouseEvent)
  {
    if ((paramMouseEvent.getAction() == 4) || (paramMouseEvent.getAction() == 5))
    {
      this.pmouseX = this.emouseX;
      this.pmouseY = this.emouseY;
      this.mouseX = paramMouseEvent.getX();
      this.mouseY = paramMouseEvent.getY();
    }
    if (paramMouseEvent.getAction() == 1)
    {
      this.mouseX = paramMouseEvent.getX();
      this.mouseY = paramMouseEvent.getY();
      this.pmouseX = this.mouseX;
      this.pmouseY = this.mouseY;
      this.dmouseX = this.mouseX;
      this.dmouseY = this.mouseY;
    }
    switch (paramMouseEvent.getAction())
    {
    default: 
      handleMethods("mouseEvent", new Object[] { paramMouseEvent });
      switch (paramMouseEvent.getAction())
      {
      }
      break;
    }
    for (;;)
    {
      if ((paramMouseEvent.getAction() == 4) || (paramMouseEvent.getAction() == 5))
      {
        this.emouseX = this.mouseX;
        this.emouseY = this.mouseY;
      }
      if (paramMouseEvent.getAction() == 1)
      {
        this.emouseX = this.mouseX;
        this.emouseY = this.mouseY;
      }
      return;
      this.mousePressed = true;
      break;
      this.mousePressed = false;
      break;
      mousePressed(paramMouseEvent);
      continue;
      mouseReleased(paramMouseEvent);
      continue;
      mouseClicked(paramMouseEvent);
      continue;
      mouseDragged(paramMouseEvent);
      continue;
      mouseMoved(paramMouseEvent);
      continue;
      mouseEntered(paramMouseEvent);
      continue;
      mouseExited(paramMouseEvent);
    }
  }
  
  public void hint(int paramInt)
  {
    this.g.hint(paramInt);
  }
  
  public final float hue(int paramInt)
  {
    return this.g.hue(paramInt);
  }
  
  public void image(PImage paramPImage, float paramFloat1, float paramFloat2)
  {
    this.g.image(paramPImage, paramFloat1, paramFloat2);
  }
  
  public void image(PImage paramPImage, float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.image(paramPImage, paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void image(PImage paramPImage, float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, int paramInt1, int paramInt2, int paramInt3, int paramInt4)
  {
    this.g.image(paramPImage, paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramInt1, paramInt2, paramInt3, paramInt4);
  }
  
  public void imageMode(int paramInt)
  {
    this.g.imageMode(paramInt);
  }
  
  protected String insertFrame(String paramString)
  {
    int i = paramString.indexOf('#');
    int j = paramString.lastIndexOf('#');
    String str = paramString;
    if (i != -1)
    {
      str = paramString;
      if (j - i > 0)
      {
        str = paramString.substring(0, i);
        paramString = paramString.substring(j + 1);
        str = str + nf(this.frameCount, j - i + 1) + paramString;
      }
    }
    return str;
  }
  
  public boolean isGL()
  {
    return this.g.isGL();
  }
  
  public void keyPressed() {}
  
  public void keyPressed(processing.event.KeyEvent paramKeyEvent)
  {
    keyPressed();
  }
  
  public void keyReleased() {}
  
  public void keyReleased(processing.event.KeyEvent paramKeyEvent)
  {
    keyReleased();
  }
  
  public void keyTyped() {}
  
  public void keyTyped(processing.event.KeyEvent paramKeyEvent)
  {
    keyTyped();
  }
  
  public int lerpColor(int paramInt1, int paramInt2, float paramFloat)
  {
    return this.g.lerpColor(paramInt1, paramInt2, paramFloat);
  }
  
  public void lightFalloff(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.lightFalloff(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void lightSpecular(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.lightSpecular(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void lights()
  {
    this.g.lights();
  }
  
  public void line(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.line(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void line(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.line(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public void link(String paramString)
  {
    link(paramString, null);
  }
  
  public void link(String paramString1, String paramString2)
  {
    startActivity(new Intent("android.intent.action.VIEW", Uri.parse(paramString1)));
  }
  
  public byte[] loadBytes(String paramString)
  {
    InputStream localInputStream = createInput(paramString);
    if (localInputStream != null) {
      return loadBytes(localInputStream);
    }
    System.err.println("The file \"" + paramString + "\" " + "is missing or inaccessible, make sure " + "the URL is valid or that the file has been " + "added to your sketch and is readable.");
    return null;
  }
  
  public PFont loadFont(String paramString)
  {
    try
    {
      PFont localPFont = new PFont(createInput(paramString));
      return localPFont;
    }
    catch (Exception localException)
    {
      die("Could not load font " + paramString + ". " + "Make sure that the font has been copied " + "to the data folder of your sketch.", localException);
    }
    return null;
  }
  
  /* Error */
  public PImage loadImage(String paramString)
  {
    // Byte code:
    //   0: aload_0
    //   1: aload_1
    //   2: invokevirtual 1710	processing/core/PApplet:createInput	(Ljava/lang/String;)Ljava/io/InputStream;
    //   5: astore_2
    //   6: aload_2
    //   7: ifnonnull +37 -> 44
    //   10: getstatic 522	java/lang/System:err	Ljava/io/PrintStream;
    //   13: new 429	java/lang/StringBuilder
    //   16: dup
    //   17: invokespecial 430	java/lang/StringBuilder:<init>	()V
    //   20: ldc_w 2162
    //   23: invokevirtual 435	java/lang/StringBuilder:append	(Ljava/lang/String;)Ljava/lang/StringBuilder;
    //   26: aload_1
    //   27: invokevirtual 435	java/lang/StringBuilder:append	(Ljava/lang/String;)Ljava/lang/StringBuilder;
    //   30: ldc_w 1138
    //   33: invokevirtual 435	java/lang/StringBuilder:append	(Ljava/lang/String;)Ljava/lang/StringBuilder;
    //   36: invokevirtual 439	java/lang/StringBuilder:toString	()Ljava/lang/String;
    //   39: invokevirtual 532	java/io/PrintStream:println	(Ljava/lang/String;)V
    //   42: aconst_null
    //   43: areturn
    //   44: aload_2
    //   45: invokestatic 2168	android/graphics/BitmapFactory:decodeStream	(Ljava/io/InputStream;)Landroid/graphics/Bitmap;
    //   48: astore_1
    //   49: aload_2
    //   50: invokevirtual 2171	java/io/InputStream:close	()V
    //   53: new 443	processing/core/PImage
    //   56: dup
    //   57: aload_1
    //   58: invokespecial 2173	processing/core/PImage:<init>	(Ljava/lang/Object;)V
    //   61: astore_1
    //   62: aload_1
    //   63: aload_0
    //   64: putfield 1645	processing/core/PImage:parent	Lprocessing/core/PApplet;
    //   67: aload_1
    //   68: areturn
    //   69: astore_1
    //   70: aload_2
    //   71: invokevirtual 2171	java/io/InputStream:close	()V
    //   74: aload_1
    //   75: athrow
    //   76: astore_2
    //   77: goto -24 -> 53
    //   80: astore_2
    //   81: goto -7 -> 74
    // Local variable table:
    //   start	length	slot	name	signature
    //   0	84	0	this	PApplet
    //   0	84	1	paramString	String
    //   5	66	2	localInputStream	InputStream
    //   76	1	2	localIOException1	IOException
    //   80	1	2	localIOException2	IOException
    // Exception table:
    //   from	to	target	type
    //   44	49	69	finally
    //   49	53	76	java/io/IOException
    //   70	74	80	java/io/IOException
  }
  
  public void loadPixels()
  {
    this.g.loadPixels();
    this.pixels = this.g.pixels;
  }
  
  public PShader loadShader(String paramString)
  {
    return this.g.loadShader(paramString);
  }
  
  public PShader loadShader(String paramString1, String paramString2)
  {
    return this.g.loadShader(paramString1, paramString2);
  }
  
  public PShape loadShape(String paramString)
  {
    return this.g.loadShape(paramString);
  }
  
  public String[] loadStrings(String paramString)
  {
    InputStream localInputStream = createInput(paramString);
    if (localInputStream != null) {
      return loadStrings(localInputStream);
    }
    System.err.println("The file \"" + paramString + "\" " + "is missing or inaccessible, make sure " + "the URL is valid or that the file has been " + "added to your sketch and is readable.");
    return null;
  }
  
  public Table loadTable(String paramString)
  {
    return loadTable(paramString, null);
  }
  
  public Table loadTable(String paramString1, String paramString2)
  {
    for (;;)
    {
      String str2;
      try
      {
        str2 = checkExtension(paramString1);
        str1 = paramString2;
        if (str2 != null)
        {
          if (str2.equals("csv")) {
            break label90;
          }
          str1 = paramString2;
          if (str2.equals("tsv")) {
            break label90;
          }
        }
        return new Table(createInput(paramString1), str1);
      }
      catch (IOException paramString1)
      {
        paramString1.printStackTrace();
        return null;
      }
      String str1 = str2 + "," + paramString2;
      continue;
      label90:
      if (paramString2 == null) {
        str1 = str2;
      }
    }
  }
  
  public XML loadXML(String paramString)
  {
    return loadXML(paramString, null);
  }
  
  public XML loadXML(String paramString1, String paramString2)
  {
    try
    {
      paramString1 = new XML(createInput(paramString1), paramString2);
      return paramString1;
    }
    catch (Exception paramString1)
    {
      paramString1.printStackTrace();
    }
    return null;
  }
  
  public void loop()
  {
    try
    {
      if (!this.looping) {
        this.looping = true;
      }
      return;
    }
    finally
    {
      localObject = finally;
      throw ((Throwable)localObject);
    }
  }
  
  public void mask(PImage paramPImage)
  {
    this.g.mask(paramPImage);
  }
  
  public void mask(int[] paramArrayOfInt)
  {
    this.g.mask(paramArrayOfInt);
  }
  
  public void method(String paramString)
  {
    try
    {
      getClass().getMethod(paramString, new Class[0]).invoke(this, new Object[0]);
      return;
    }
    catch (IllegalArgumentException paramString)
    {
      paramString.printStackTrace();
      return;
    }
    catch (IllegalAccessException paramString)
    {
      paramString.printStackTrace();
      return;
    }
    catch (InvocationTargetException paramString)
    {
      paramString.getTargetException().printStackTrace();
      return;
    }
    catch (NoSuchMethodException localNoSuchMethodException)
    {
      System.err.println("There is no public " + paramString + "() method " + "in the class " + getClass().getName());
      return;
    }
    catch (Exception paramString)
    {
      paramString.printStackTrace();
    }
  }
  
  public int millis()
  {
    return (int)(System.currentTimeMillis() - this.millisOffset);
  }
  
  public float modelX(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return this.g.modelX(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public float modelY(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return this.g.modelY(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public float modelZ(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return this.g.modelZ(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void mouseClicked() {}
  
  public void mouseClicked(MouseEvent paramMouseEvent)
  {
    mouseClicked();
  }
  
  public void mouseDragged() {}
  
  public void mouseDragged(MouseEvent paramMouseEvent)
  {
    mouseDragged();
  }
  
  public void mouseEntered() {}
  
  public void mouseEntered(MouseEvent paramMouseEvent)
  {
    mouseEntered();
  }
  
  public void mouseExited() {}
  
  public void mouseExited(MouseEvent paramMouseEvent)
  {
    mouseExited();
  }
  
  public void mouseMoved() {}
  
  public void mouseMoved(MouseEvent paramMouseEvent)
  {
    mouseMoved();
  }
  
  public void mousePressed() {}
  
  public void mousePressed(MouseEvent paramMouseEvent)
  {
    mousePressed();
  }
  
  public void mouseReleased() {}
  
  public void mouseReleased(MouseEvent paramMouseEvent)
  {
    mouseReleased();
  }
  
  protected void nativeKeyEvent(android.view.KeyEvent paramKeyEvent)
  {
    int k = 1;
    int j = (char)paramKeyEvent.getUnicodeChar();
    int i;
    if (j != 0)
    {
      i = j;
      if (j != 65535) {}
    }
    else
    {
      i = 65535;
    }
    int m = paramKeyEvent.getKeyCode();
    int n = paramKeyEvent.getAction();
    if (n == 0) {}
    for (;;)
    {
      postEvent(new processing.event.KeyEvent(paramKeyEvent, paramKeyEvent.getEventTime(), k, 0, i, m));
      return;
      if (n == 1) {
        k = 2;
      } else {
        k = 0;
      }
    }
  }
  
  protected void nativeMotionEvent(MotionEvent paramMotionEvent)
  {
    int k = paramMotionEvent.getMetaState();
    int j = 0;
    if ((k & 0x1) != 0) {
      j = 1;
    }
    int i = j;
    if ((k & 0x1000) != 0) {
      i = j | 0x2;
    }
    j = i;
    if ((0x10000 & k) != 0) {
      j = i | 0x4;
    }
    i = j;
    if ((k & 0x2) != 0) {
      i = j | 0x8;
    }
    switch (paramMotionEvent.getAction())
    {
    }
    do
    {
      do
      {
        return;
        this.motionPointerId = paramMotionEvent.getPointerId(0);
        postEvent(new MouseEvent(paramMotionEvent, paramMotionEvent.getEventTime(), 1, i, (int)paramMotionEvent.getX(), (int)paramMotionEvent.getY(), 21, 1));
        return;
        j = paramMotionEvent.findPointerIndex(this.motionPointerId);
      } while (j == -1);
      postEvent(new MouseEvent(paramMotionEvent, paramMotionEvent.getEventTime(), 4, i, (int)paramMotionEvent.getX(j), (int)paramMotionEvent.getY(j), 21, 1));
      return;
      j = paramMotionEvent.findPointerIndex(this.motionPointerId);
    } while (j == -1);
    postEvent(new MouseEvent(paramMotionEvent, paramMotionEvent.getEventTime(), 2, i, (int)paramMotionEvent.getX(j), (int)paramMotionEvent.getY(j), 21, 1));
  }
  
  public void noClip()
  {
    this.g.noClip();
  }
  
  public void noFill()
  {
    this.g.noFill();
  }
  
  public void noLights()
  {
    this.g.noLights();
  }
  
  public void noLoop()
  {
    try
    {
      if (this.looping) {
        this.looping = false;
      }
      return;
    }
    finally
    {
      localObject = finally;
      throw ((Throwable)localObject);
    }
  }
  
  public void noSmooth()
  {
    this.g.noSmooth();
  }
  
  public void noStroke()
  {
    this.g.noStroke();
  }
  
  public void noTexture()
  {
    this.g.noTexture();
  }
  
  public void noTint()
  {
    this.g.noTint();
  }
  
  public float noise(float paramFloat)
  {
    return noise(paramFloat, 0.0F, 0.0F);
  }
  
  public float noise(float paramFloat1, float paramFloat2)
  {
    return noise(paramFloat1, paramFloat2, 0.0F);
  }
  
  public float noise(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    if (this.perlin == null)
    {
      if (this.perlinRandom == null) {
        this.perlinRandom = new Random();
      }
      this.perlin = new float['?'];
      i = 0;
      while (i < 4096)
      {
        this.perlin[i] = this.perlinRandom.nextFloat();
        i += 1;
      }
      this.perlin_cosTable = PGraphics.cosLUT;
      this.perlin_PI = 720;
      this.perlin_TWOPI = 720;
      this.perlin_PI >>= 1;
    }
    float f1 = paramFloat1;
    if (paramFloat1 < 0.0F) {
      f1 = -paramFloat1;
    }
    paramFloat1 = paramFloat2;
    if (paramFloat2 < 0.0F) {
      paramFloat1 = -paramFloat2;
    }
    paramFloat2 = paramFloat3;
    if (paramFloat3 < 0.0F) {
      paramFloat2 = -paramFloat3;
    }
    int i = (int)f1;
    int j = (int)paramFloat1;
    int k = (int)paramFloat2;
    paramFloat3 = f1 - i;
    float f3 = paramFloat1 - j;
    float f4 = paramFloat2 - k;
    float f2 = 0.0F;
    f1 = 0.5F;
    int m = 0;
    paramFloat1 = paramFloat3;
    paramFloat2 = f3;
    paramFloat3 = f4;
    while (m < this.perlin_octaves)
    {
      int n = (j << 4) + i + (k << 8);
      f3 = noise_fsc(paramFloat1);
      f4 = noise_fsc(paramFloat2);
      float f5 = this.perlin[(n & 0xFFF)];
      f5 += (this.perlin[(n + 1 & 0xFFF)] - f5) * f3;
      float f6 = this.perlin[(n + 16 & 0xFFF)];
      f5 += (f6 + (this.perlin[(n + 16 + 1 & 0xFFF)] - f6) * f3 - f5) * f4;
      n += 256;
      f6 = this.perlin[(n & 0xFFF)];
      f6 += (this.perlin[(n + 1 & 0xFFF)] - f6) * f3;
      float f7 = this.perlin[(n + 16 & 0xFFF)];
      f2 += ((((this.perlin[(n + 16 + 1 & 0xFFF)] - f7) * f3 + f7 - f6) * f4 + f6 - f5) * noise_fsc(paramFloat3) + f5) * f1;
      f1 *= this.perlin_amp_falloff;
      int i2 = i << 1;
      f5 = paramFloat1 * 2.0F;
      int i1 = j << 1;
      f4 = paramFloat2 * 2.0F;
      n = k << 1;
      f3 = paramFloat3 * 2.0F;
      paramFloat1 = f5;
      i = i2;
      if (f5 >= 1.0F)
      {
        i = i2 + 1;
        paramFloat1 = f5 - 1.0F;
      }
      paramFloat2 = f4;
      j = i1;
      if (f4 >= 1.0F)
      {
        j = i1 + 1;
        paramFloat2 = f4 - 1.0F;
      }
      paramFloat3 = f3;
      k = n;
      if (f3 >= 1.0F)
      {
        k = n + 1;
        paramFloat3 = f3 - 1.0F;
      }
      m += 1;
    }
    return f2;
  }
  
  public void noiseDetail(int paramInt)
  {
    if (paramInt > 0) {
      this.perlin_octaves = paramInt;
    }
  }
  
  public void noiseDetail(int paramInt, float paramFloat)
  {
    if (paramInt > 0) {
      this.perlin_octaves = paramInt;
    }
    if (paramFloat > 0.0F) {
      this.perlin_amp_falloff = paramFloat;
    }
  }
  
  public void noiseSeed(long paramLong)
  {
    if (this.perlinRandom == null) {
      this.perlinRandom = new Random();
    }
    this.perlinRandom.setSeed(paramLong);
    this.perlin = null;
  }
  
  public void normal(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.normal(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void onBackPressed()
  {
    exit();
  }
  
  public void onConfigurationChanged(Configuration paramConfiguration)
  {
    super.onConfigurationChanged(paramConfiguration);
  }
  
  public void onCreate(Bundle paramBundle)
  {
    super.onCreate(paramBundle);
    paramBundle = getWindow();
    requestWindowFeature(1);
    paramBundle.setFlags(256, 256);
    paramBundle.setFlags(1024, 1024);
    Object localObject = new DisplayMetrics();
    getWindowManager().getDefaultDisplay().getMetrics((DisplayMetrics)localObject);
    this.displayWidth = ((DisplayMetrics)localObject).widthPixels;
    this.displayHeight = ((DisplayMetrics)localObject).heightPixels;
    int i = sketchWidth();
    int j = sketchHeight();
    if (sketchRenderer().equals("processing.core.PGraphicsAndroid2D"))
    {
      this.surfaceView = new SketchSurfaceView(this, i, j);
      if ((i != this.displayWidth) || (j != this.displayHeight)) {
        break label238;
      }
      paramBundle.setContentView(this.surfaceView);
    }
    for (;;)
    {
      this.finished = false;
      this.looping = true;
      this.redraw = true;
      this.sketchPath = getApplicationContext().getFilesDir().getAbsolutePath();
      this.handler = new Handler();
      start();
      return;
      if ((!sketchRenderer().equals("processing.opengl.PGraphics2D")) && (!sketchRenderer().equals("processing.opengl.PGraphics3D"))) {
        break;
      }
      this.surfaceView = new SketchSurfaceViewGL(this, i, j, sketchRenderer().equals("processing.opengl.PGraphics3D"));
      break;
      label238:
      localObject = new RelativeLayout(this);
      RelativeLayout.LayoutParams localLayoutParams = new RelativeLayout.LayoutParams(-2, -2);
      localLayoutParams.addRule(13);
      LinearLayout localLinearLayout = new LinearLayout(this);
      localLinearLayout.addView(this.surfaceView, sketchWidth(), sketchHeight());
      ((RelativeLayout)localObject).addView(localLinearLayout, localLayoutParams);
      paramBundle.setContentView((View)localObject);
    }
  }
  
  public void onDestroy()
  {
    dispose();
    super.onDestroy();
  }
  
  protected void onPause()
  {
    super.onPause();
    this.paused = true;
    handleMethods("pause");
    pause();
  }
  
  protected void onResume()
  {
    super.onResume();
    this.paused = false;
    handleMethods("resume");
    resume();
  }
  
  protected void onStart()
  {
    tellPDE("onStart");
    super.onStart();
  }
  
  protected void onStop()
  {
    tellPDE("onStop");
    super.onStop();
  }
  
  public void orientation(int paramInt)
  {
    if (paramInt == 1) {
      setRequestedOrientation(1);
    }
    while (paramInt != 2) {
      return;
    }
    setRequestedOrientation(0);
  }
  
  public void ortho()
  {
    this.g.ortho();
  }
  
  public void ortho(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.ortho(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void ortho(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.ortho(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public XML parseXML(String paramString)
  {
    return parseXML(paramString, null);
  }
  
  public XML parseXML(String paramString1, String paramString2)
  {
    try
    {
      paramString1 = XML.parse(paramString1, paramString2);
      return paramString1;
    }
    catch (Exception paramString1)
    {
      paramString1.printStackTrace();
    }
    return null;
  }
  
  public void pause() {}
  
  public void perspective()
  {
    this.g.perspective();
  }
  
  public void perspective(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.perspective(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void point(float paramFloat1, float paramFloat2)
  {
    this.g.point(paramFloat1, paramFloat2);
  }
  
  public void point(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.point(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void pointLight(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.pointLight(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public void popMatrix()
  {
    this.g.popMatrix();
  }
  
  public void popStyle()
  {
    this.g.popStyle();
  }
  
  public void postEvent(Event paramEvent)
  {
    this.eventQueue.add(paramEvent);
    if (!this.looping) {
      dequeueEvents();
    }
  }
  
  public void printCamera()
  {
    this.g.printCamera();
  }
  
  public void printMatrix()
  {
    this.g.printMatrix();
  }
  
  public void printProjection()
  {
    this.g.printProjection();
  }
  
  public void pushMatrix()
  {
    this.g.pushMatrix();
  }
  
  public void pushStyle()
  {
    this.g.pushStyle();
  }
  
  public void quad(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8)
  {
    this.g.quad(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8);
  }
  
  public void quadraticVertex(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.quadraticVertex(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void quadraticVertex(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.quadraticVertex(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  public final float random(float paramFloat)
  {
    if (paramFloat == 0.0F) {
      return 0.0F;
    }
    if (this.internalRandom == null) {
      this.internalRandom = new Random();
    }
    float f;
    do
    {
      f = this.internalRandom.nextFloat() * paramFloat;
    } while (f == paramFloat);
    return f;
  }
  
  public final float random(float paramFloat1, float paramFloat2)
  {
    if (paramFloat1 >= paramFloat2) {
      return paramFloat1;
    }
    return paramFloat1 + random(paramFloat2 - paramFloat1);
  }
  
  public final void randomSeed(long paramLong)
  {
    if (this.internalRandom == null) {
      this.internalRandom = new Random();
    }
    this.internalRandom.setSeed(paramLong);
  }
  
  public void rect(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.rect(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void rect(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    this.g.rect(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5);
  }
  
  public void rect(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8)
  {
    this.g.rect(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8);
  }
  
  public void rectMode(int paramInt)
  {
    this.g.rectMode(paramInt);
  }
  
  public final float red(int paramInt)
  {
    return this.g.red(paramInt);
  }
  
  public void redraw()
  {
    try
    {
      if (!this.looping) {
        this.redraw = true;
      }
      return;
    }
    finally
    {
      localObject = finally;
      throw ((Throwable)localObject);
    }
  }
  
  @Deprecated
  public void registerDispose(Object paramObject)
  {
    registerNoArgs("dispose", paramObject);
  }
  
  @Deprecated
  public void registerDraw(Object paramObject)
  {
    registerNoArgs("draw", paramObject);
  }
  
  public void registerMethod(String paramString, Object paramObject)
  {
    if (paramString.equals("mouseEvent"))
    {
      registerWithArgs("mouseEvent", paramObject, new Class[] { MouseEvent.class });
      return;
    }
    if (paramString.equals("keyEvent"))
    {
      registerWithArgs("keyEvent", paramObject, new Class[] { processing.event.KeyEvent.class });
      return;
    }
    if (paramString.equals("touchEvent"))
    {
      registerWithArgs("touchEvent", paramObject, new Class[] { TouchEvent.class });
      return;
    }
    registerNoArgs(paramString, paramObject);
  }
  
  @Deprecated
  public void registerPost(Object paramObject)
  {
    registerNoArgs("post", paramObject);
  }
  
  @Deprecated
  public void registerPre(Object paramObject)
  {
    registerNoArgs("pre", paramObject);
  }
  
  @Deprecated
  public void registerSize(Object paramObject)
  {
    System.err.println("The registerSize() command is no longer supported.");
  }
  
  public void removeCache(PImage paramPImage)
  {
    this.g.removeCache(paramPImage);
  }
  
  public PImage requestImage(String paramString)
  {
    PImage localPImage = createImage(0, 0, 2);
    new AsyncImageLoader(paramString, localPImage).start();
    return localPImage;
  }
  
  public void resetMatrix()
  {
    this.g.resetMatrix();
  }
  
  public void resetShader()
  {
    this.g.resetShader();
  }
  
  public void resetShader(int paramInt)
  {
    this.g.resetShader(paramInt);
  }
  
  public void resume() {}
  
  public void rotate(float paramFloat)
  {
    this.g.rotate(paramFloat);
  }
  
  public void rotate(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.rotate(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void rotateX(float paramFloat)
  {
    this.g.rotateX(paramFloat);
  }
  
  public void rotateY(float paramFloat)
  {
    this.g.rotateY(paramFloat);
  }
  
  public void rotateZ(float paramFloat)
  {
    this.g.rotateZ(paramFloat);
  }
  
  public void run()
  {
    long l2 = System.nanoTime();
    long l1 = 0L;
    long l3;
    if ((Thread.currentThread() == this.thread) && (!this.finished))
    {
      while (this.paused) {
        try
        {
          Thread.sleep(100L);
        }
        catch (InterruptedException localInterruptedException1) {}
      }
      if (this.g != null) {
        this.g.requestDraw();
      }
      l3 = System.nanoTime();
      l1 = this.frameRatePeriod - (l3 - l2) - l1;
      if (l1 <= 0L) {
        break label139;
      }
    }
    for (;;)
    {
      try
      {
        Thread.sleep(l1 / 1000000L, (int)(l1 % 1000000L));
        l1 = System.nanoTime() - l3 - l1;
        l2 = System.nanoTime();
        break;
        if (!this.paused)
        {
          stop();
          if (this.exitCalled) {
            exit2();
          }
        }
        return;
      }
      catch (InterruptedException localInterruptedException2)
      {
        continue;
      }
      label139:
      l1 = 0L;
    }
  }
  
  public final float saturation(int paramInt)
  {
    return this.g.saturation(paramInt);
  }
  
  public void save(String paramString)
  {
    this.g.save(savePath(paramString));
  }
  
  public void saveBytes(String paramString, byte[] paramArrayOfByte)
  {
    saveBytes(saveFile(paramString), paramArrayOfByte);
  }
  
  public File saveFile(String paramString)
  {
    return new File(savePath(paramString));
  }
  
  public void saveFrame()
  {
    try
    {
      this.g.save(savePath("screen-" + nf(this.frameCount, 4) + ".tif"));
      return;
    }
    catch (SecurityException localSecurityException)
    {
      System.err.println("Can't use saveFrame() when running in a browser, unless using a signed applet.");
    }
  }
  
  public void saveFrame(String paramString)
  {
    try
    {
      this.g.save(savePath(insertFrame(paramString)));
      return;
    }
    catch (SecurityException paramString)
    {
      System.err.println("Can't use saveFrame() when running in a browser, unless using a signed applet.");
    }
  }
  
  public String savePath(String paramString)
  {
    if (paramString == null) {
      return null;
    }
    paramString = sketchPath(paramString);
    createPath(paramString);
    return paramString;
  }
  
  public boolean saveStream(File paramFile, String paramString)
  {
    return saveStream(paramFile, createInputRaw(paramString));
  }
  
  public boolean saveStream(String paramString, InputStream paramInputStream)
  {
    return saveStream(saveFile(paramString), paramInputStream);
  }
  
  public boolean saveStream(String paramString1, String paramString2)
  {
    return saveStream(saveFile(paramString1), paramString2);
  }
  
  public void saveStrings(String paramString, String[] paramArrayOfString)
  {
    saveStrings(saveFile(paramString), paramArrayOfString);
  }
  
  public boolean saveTable(Table paramTable, String paramString)
  {
    return saveTable(paramTable, paramString, null);
  }
  
  public boolean saveTable(Table paramTable, String paramString1, String paramString2)
  {
    try
    {
      paramTable.save(saveFile(paramString1), paramString2);
      return true;
    }
    catch (IOException paramTable)
    {
      paramTable.printStackTrace();
    }
    return false;
  }
  
  public boolean saveXML(XML paramXML, String paramString)
  {
    return saveXML(paramXML, paramString, null);
  }
  
  public boolean saveXML(XML paramXML, String paramString1, String paramString2)
  {
    return paramXML.save(saveFile(paramString1), paramString2);
  }
  
  public void scale(float paramFloat)
  {
    this.g.scale(paramFloat);
  }
  
  public void scale(float paramFloat1, float paramFloat2)
  {
    this.g.scale(paramFloat1, paramFloat2);
  }
  
  public void scale(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.scale(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public float screenX(float paramFloat1, float paramFloat2)
  {
    return this.g.screenX(paramFloat1, paramFloat2);
  }
  
  public float screenX(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return this.g.screenX(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public float screenY(float paramFloat1, float paramFloat2)
  {
    return this.g.screenY(paramFloat1, paramFloat2);
  }
  
  public float screenY(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return this.g.screenY(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public float screenZ(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    return this.g.screenZ(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void set(int paramInt1, int paramInt2, int paramInt3)
  {
    this.g.set(paramInt1, paramInt2, paramInt3);
  }
  
  public void set(int paramInt1, int paramInt2, PImage paramPImage)
  {
    this.g.set(paramInt1, paramInt2, paramPImage);
  }
  
  public void setCache(PImage paramPImage, Object paramObject)
  {
    this.g.setCache(paramPImage, paramObject);
  }
  
  public void setMatrix(PMatrix2D paramPMatrix2D)
  {
    this.g.setMatrix(paramPMatrix2D);
  }
  
  public void setMatrix(PMatrix3D paramPMatrix3D)
  {
    this.g.setMatrix(paramPMatrix3D);
  }
  
  public void setMatrix(PMatrix paramPMatrix)
  {
    this.g.setMatrix(paramPMatrix);
  }
  
  public void setup() {}
  
  public void shader(PShader paramPShader)
  {
    this.g.shader(paramPShader);
  }
  
  public void shader(PShader paramPShader, int paramInt)
  {
    this.g.shader(paramPShader, paramInt);
  }
  
  public void shape(PShape paramPShape)
  {
    this.g.shape(paramPShape);
  }
  
  public void shape(PShape paramPShape, float paramFloat1, float paramFloat2)
  {
    this.g.shape(paramPShape, paramFloat1, paramFloat2);
  }
  
  public void shape(PShape paramPShape, float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.shape(paramPShape, paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void shapeMode(int paramInt)
  {
    this.g.shapeMode(paramInt);
  }
  
  public void shearX(float paramFloat)
  {
    this.g.shearX(paramFloat);
  }
  
  public void shearY(float paramFloat)
  {
    this.g.shearY(paramFloat);
  }
  
  public void shininess(float paramFloat)
  {
    this.g.shininess(paramFloat);
  }
  
  public void size(int paramInt1, int paramInt2)
  {
    size(paramInt1, paramInt2, "processing.opengl.PGraphics2D", null);
  }
  
  public void size(int paramInt1, int paramInt2, String paramString)
  {
    size(paramInt1, paramInt2, paramString, null);
  }
  
  public void size(int paramInt1, int paramInt2, String paramString1, String paramString2)
  {
    System.out.println("This size() method is ignored on Android.");
    System.out.println("See http://wiki.processing.org/w/Android for more information.");
  }
  
  public File sketchFile(String paramString)
  {
    return new File(sketchPath(paramString));
  }
  
  public int sketchHeight()
  {
    return this.displayHeight;
  }
  
  public String sketchPath(String paramString)
  {
    if (this.sketchPath == null) {}
    for (;;)
    {
      return paramString;
      try
      {
        boolean bool = new File(paramString).isAbsolute();
        if (bool) {}
      }
      catch (Exception localException)
      {
        for (;;) {}
      }
    }
    return getApplicationContext().getFileStreamPath(paramString).getAbsolutePath();
  }
  
  public int sketchQuality()
  {
    return 1;
  }
  
  public String sketchRenderer()
  {
    return "processing.core.PGraphicsAndroid2D";
  }
  
  public int sketchWidth()
  {
    return this.displayWidth;
  }
  
  public void smooth()
  {
    this.g.smooth();
  }
  
  public void smooth(int paramInt)
  {
    this.g.smooth(paramInt);
  }
  
  public void specular(float paramFloat)
  {
    this.g.specular(paramFloat);
  }
  
  public void specular(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.specular(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void specular(int paramInt)
  {
    this.g.specular(paramInt);
  }
  
  public void sphere(float paramFloat)
  {
    this.g.sphere(paramFloat);
  }
  
  public void sphereDetail(int paramInt)
  {
    this.g.sphereDetail(paramInt);
  }
  
  public void sphereDetail(int paramInt1, int paramInt2)
  {
    this.g.sphereDetail(paramInt1, paramInt2);
  }
  
  public void spotLight(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6, float paramFloat7, float paramFloat8, float paramFloat9, float paramFloat10, float paramFloat11)
  {
    this.g.spotLight(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6, paramFloat7, paramFloat8, paramFloat9, paramFloat10, paramFloat11);
  }
  
  public void start()
  {
    this.finished = false;
    this.paused = false;
    if (this.thread == null)
    {
      this.thread = new Thread(this, "Animation Thread");
      this.thread.start();
    }
  }
  
  public void stop()
  {
    this.paused = true;
  }
  
  public void stroke(float paramFloat)
  {
    this.g.stroke(paramFloat);
  }
  
  public void stroke(float paramFloat1, float paramFloat2)
  {
    this.g.stroke(paramFloat1, paramFloat2);
  }
  
  public void stroke(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.stroke(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void stroke(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.stroke(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void stroke(int paramInt)
  {
    this.g.stroke(paramInt);
  }
  
  public void stroke(int paramInt, float paramFloat)
  {
    this.g.stroke(paramInt, paramFloat);
  }
  
  public void strokeCap(int paramInt)
  {
    this.g.strokeCap(paramInt);
  }
  
  public void strokeJoin(int paramInt)
  {
    this.g.strokeJoin(paramInt);
  }
  
  public void strokeWeight(float paramFloat)
  {
    this.g.strokeWeight(paramFloat);
  }
  
  public void style(PStyle paramPStyle)
  {
    this.g.style(paramPStyle);
  }
  
  public boolean surfaceKeyDown(int paramInt, android.view.KeyEvent paramKeyEvent)
  {
    nativeKeyEvent(paramKeyEvent);
    return super.onKeyDown(paramInt, paramKeyEvent);
  }
  
  public boolean surfaceKeyUp(int paramInt, android.view.KeyEvent paramKeyEvent)
  {
    nativeKeyEvent(paramKeyEvent);
    return super.onKeyUp(paramInt, paramKeyEvent);
  }
  
  public boolean surfaceTouchEvent(MotionEvent paramMotionEvent)
  {
    nativeMotionEvent(paramMotionEvent);
    return true;
  }
  
  public void surfaceWindowFocusChanged(boolean paramBoolean)
  {
    super.onWindowFocusChanged(paramBoolean);
    this.focused = paramBoolean;
    if (this.focused)
    {
      focusGained();
      return;
    }
    focusLost();
  }
  
  public void text(char paramChar, float paramFloat1, float paramFloat2)
  {
    this.g.text(paramChar, paramFloat1, paramFloat2);
  }
  
  public void text(char paramChar, float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.text(paramChar, paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void text(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.text(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void text(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.text(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void text(int paramInt, float paramFloat1, float paramFloat2)
  {
    this.g.text(paramInt, paramFloat1, paramFloat2);
  }
  
  public void text(int paramInt, float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.text(paramInt, paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void text(String paramString, float paramFloat1, float paramFloat2)
  {
    this.g.text(paramString, paramFloat1, paramFloat2);
  }
  
  public void text(String paramString, float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.text(paramString, paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void text(String paramString, float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.text(paramString, paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void textAlign(int paramInt)
  {
    this.g.textAlign(paramInt);
  }
  
  public void textAlign(int paramInt1, int paramInt2)
  {
    this.g.textAlign(paramInt1, paramInt2);
  }
  
  public float textAscent()
  {
    return this.g.textAscent();
  }
  
  public float textDescent()
  {
    return this.g.textDescent();
  }
  
  public void textFont(PFont paramPFont)
  {
    this.g.textFont(paramPFont);
  }
  
  public void textFont(PFont paramPFont, float paramFloat)
  {
    this.g.textFont(paramPFont, paramFloat);
  }
  
  public void textLeading(float paramFloat)
  {
    this.g.textLeading(paramFloat);
  }
  
  public void textMode(int paramInt)
  {
    this.g.textMode(paramInt);
  }
  
  public void textSize(float paramFloat)
  {
    this.g.textSize(paramFloat);
  }
  
  public float textWidth(char paramChar)
  {
    return this.g.textWidth(paramChar);
  }
  
  public float textWidth(String paramString)
  {
    return this.g.textWidth(paramString);
  }
  
  public void texture(PImage paramPImage)
  {
    this.g.texture(paramPImage);
  }
  
  public void textureMode(int paramInt)
  {
    this.g.textureMode(paramInt);
  }
  
  public void textureWrap(int paramInt)
  {
    this.g.textureWrap(paramInt);
  }
  
  public void thread(final String paramString)
  {
    new Thread()
    {
      public void run()
      {
        PApplet.this.method(paramString);
      }
    }.start();
  }
  
  public void tint(float paramFloat)
  {
    this.g.tint(paramFloat);
  }
  
  public void tint(float paramFloat1, float paramFloat2)
  {
    this.g.tint(paramFloat1, paramFloat2);
  }
  
  public void tint(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.tint(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void tint(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.tint(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void tint(int paramInt)
  {
    this.g.tint(paramInt);
  }
  
  public void tint(int paramInt, float paramFloat)
  {
    this.g.tint(paramInt, paramFloat);
  }
  
  public void translate(float paramFloat1, float paramFloat2)
  {
    this.g.translate(paramFloat1, paramFloat2);
  }
  
  public void translate(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.translate(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void triangle(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5, float paramFloat6)
  {
    this.g.triangle(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5, paramFloat6);
  }
  
  @Deprecated
  public void unregisterDispose(Object paramObject)
  {
    unregisterMethod("dispose", paramObject);
  }
  
  @Deprecated
  public void unregisterDraw(Object paramObject)
  {
    unregisterMethod("draw", paramObject);
  }
  
  public void unregisterMethod(String paramString, Object paramObject)
  {
    RegisteredMethods localRegisteredMethods = (RegisteredMethods)this.registerMap.get(paramString);
    if (localRegisteredMethods == null) {
      die("No registered methods with the name " + paramString + "() were found.");
    }
    try
    {
      localRegisteredMethods.remove(paramObject);
      return;
    }
    catch (Exception localException)
    {
      die("Could not unregister " + paramString + "() for " + paramObject, localException);
    }
  }
  
  @Deprecated
  public void unregisterPost(Object paramObject)
  {
    unregisterMethod("post", paramObject);
  }
  
  @Deprecated
  public void unregisterPre(Object paramObject)
  {
    unregisterMethod("pre", paramObject);
  }
  
  @Deprecated
  public void unregisterSize(Object paramObject)
  {
    System.err.println("The unregisterSize() command is no longer supported.");
  }
  
  public void updatePixels()
  {
    this.g.updatePixels();
  }
  
  public void updatePixels(int paramInt1, int paramInt2, int paramInt3, int paramInt4)
  {
    this.g.updatePixels(paramInt1, paramInt2, paramInt3, paramInt4);
  }
  
  public void vertex(float paramFloat1, float paramFloat2)
  {
    this.g.vertex(paramFloat1, paramFloat2);
  }
  
  public void vertex(float paramFloat1, float paramFloat2, float paramFloat3)
  {
    this.g.vertex(paramFloat1, paramFloat2, paramFloat3);
  }
  
  public void vertex(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4)
  {
    this.g.vertex(paramFloat1, paramFloat2, paramFloat3, paramFloat4);
  }
  
  public void vertex(float paramFloat1, float paramFloat2, float paramFloat3, float paramFloat4, float paramFloat5)
  {
    this.g.vertex(paramFloat1, paramFloat2, paramFloat3, paramFloat4, paramFloat5);
  }
  
  public void vertex(float[] paramArrayOfFloat)
  {
    this.g.vertex(paramArrayOfFloat);
  }
  
  class AsyncImageLoader
    extends Thread
  {
    String filename;
    PImage vessel;
    
    public AsyncImageLoader(String paramString, PImage paramPImage)
    {
      this.filename = paramString;
      this.vessel = paramPImage;
    }
    
    public void run()
    {
      while (PApplet.this.requestImageCount == PApplet.this.requestImageMax) {
        try
        {
          Thread.sleep(10L);
        }
        catch (InterruptedException localInterruptedException) {}
      }
      Object localObject = PApplet.this;
      ((PApplet)localObject).requestImageCount += 1;
      localObject = PApplet.this.loadImage(this.filename);
      if (localObject == null)
      {
        this.vessel.width = -1;
        this.vessel.height = -1;
      }
      for (;;)
      {
        localObject = PApplet.this;
        ((PApplet)localObject).requestImageCount -= 1;
        return;
        this.vessel.width = ((PImage)localObject).width;
        this.vessel.height = ((PImage)localObject).height;
        this.vessel.format = ((PImage)localObject).format;
        this.vessel.pixels = ((PImage)localObject).pixels;
        this.vessel.bitmap = ((PImage)localObject).bitmap;
      }
    }
  }
  
  class InternalEventQueue
  {
    protected int count;
    protected int offset;
    protected Event[] queue = new Event[10];
    
    InternalEventQueue() {}
    
    void add(Event paramEvent)
    {
      try
      {
        if (this.count == this.queue.length) {
          this.queue = ((Event[])PApplet.expand(this.queue));
        }
        Event[] arrayOfEvent = this.queue;
        int i = this.count;
        this.count = (i + 1);
        arrayOfEvent[i] = paramEvent;
        return;
      }
      finally {}
    }
    
    /* Error */
    boolean available()
    {
      // Byte code:
      //   0: aload_0
      //   1: monitorenter
      //   2: aload_0
      //   3: getfield 30	processing/core/PApplet$InternalEventQueue:count	I
      //   6: istore_1
      //   7: iload_1
      //   8: ifeq +9 -> 17
      //   11: iconst_1
      //   12: istore_2
      //   13: aload_0
      //   14: monitorexit
      //   15: iload_2
      //   16: ireturn
      //   17: iconst_0
      //   18: istore_2
      //   19: goto -6 -> 13
      //   22: astore_3
      //   23: aload_0
      //   24: monitorexit
      //   25: aload_3
      //   26: athrow
      // Local variable table:
      //   start	length	slot	name	signature
      //   0	27	0	this	InternalEventQueue
      //   6	2	1	i	int
      //   12	7	2	bool	boolean
      //   22	4	3	localObject	Object
      // Exception table:
      //   from	to	target	type
      //   2	7	22	finally
    }
    
    Event remove()
    {
      try
      {
        if (this.offset == this.count) {
          throw new RuntimeException("Nothing left on the event queue.");
        }
      }
      finally {}
      Object localObject2 = this.queue;
      int i = this.offset;
      this.offset = (i + 1);
      localObject2 = localObject2[i];
      if (this.offset == this.count)
      {
        this.offset = 0;
        this.count = 0;
      }
      return (Event)localObject2;
    }
  }
  
  class RegisteredMethods
  {
    int count;
    Object[] emptyArgs = new Object[0];
    Method[] methods;
    Object[] objects;
    
    RegisteredMethods() {}
    
    void add(Object paramObject, Method paramMethod)
    {
      if (findIndex(paramObject) == -1)
      {
        if (this.objects == null)
        {
          this.objects = new Object[5];
          this.methods = new Method[5];
        }
        for (;;)
        {
          this.objects[this.count] = paramObject;
          this.methods[this.count] = paramMethod;
          this.count += 1;
          return;
          if (this.count == this.objects.length)
          {
            this.objects = ((Object[])PApplet.expand(this.objects));
            this.methods = ((Method[])PApplet.expand(this.methods));
          }
        }
      }
      PApplet.this.die(paramMethod.getName() + "() already added for this instance of " + paramObject.getClass().getName());
    }
    
    protected int findIndex(Object paramObject)
    {
      int i = 0;
      while (i < this.count)
      {
        if (this.objects[i] == paramObject) {
          return i;
        }
        i += 1;
      }
      return -1;
    }
    
    void handle()
    {
      handle(this.emptyArgs);
    }
    
    void handle(Object[] paramArrayOfObject)
    {
      int i = 0;
      for (;;)
      {
        if (i < this.count) {
          try
          {
            this.methods[i].invoke(this.objects[i], paramArrayOfObject);
            i += 1;
          }
          catch (Exception localException)
          {
            for (;;)
            {
              Object localObject = localException;
              if ((localException instanceof InvocationTargetException)) {
                localObject = ((InvocationTargetException)localException).getCause();
              }
              if ((localObject instanceof RuntimeException)) {
                throw ((RuntimeException)localObject);
              }
              ((Throwable)localObject).printStackTrace();
            }
          }
        }
      }
    }
    
    public void remove(Object paramObject)
    {
      int i = findIndex(paramObject);
      if (i != -1)
      {
        this.count -= 1;
        while (i < this.count)
        {
          this.objects[i] = this.objects[(i + 1)];
          this.methods[i] = this.methods[(i + 1)];
          i += 1;
        }
        this.objects[this.count] = null;
        this.methods[this.count] = null;
      }
    }
  }
  
  public static class RendererChangeException
    extends RuntimeException
  {}
  
  public class SketchSurfaceView
    extends SurfaceView
    implements SurfaceHolder.Callback
  {
    PGraphicsAndroid2D g2;
    SurfaceHolder surfaceHolder = getHolder();
    
    public SketchSurfaceView(Context paramContext, int paramInt1, int paramInt2)
    {
      super();
      this.surfaceHolder.addCallback(this);
      this.surfaceHolder.setType(2);
      this.g2 = new PGraphicsAndroid2D();
      this.g2.setSize(paramInt1, paramInt2);
      this.g2.setParent(PApplet.this);
      this.g2.setPrimary(true);
      PApplet.this.g = this.g2;
      setFocusable(true);
      setFocusableInTouchMode(true);
      requestFocus();
    }
    
    public boolean onKeyDown(int paramInt, android.view.KeyEvent paramKeyEvent)
    {
      return PApplet.this.surfaceKeyDown(paramInt, paramKeyEvent);
    }
    
    public boolean onKeyUp(int paramInt, android.view.KeyEvent paramKeyEvent)
    {
      return PApplet.this.surfaceKeyUp(paramInt, paramKeyEvent);
    }
    
    public boolean onTouchEvent(MotionEvent paramMotionEvent)
    {
      return PApplet.this.surfaceTouchEvent(paramMotionEvent);
    }
    
    public void onWindowFocusChanged(boolean paramBoolean)
    {
      PApplet.this.surfaceWindowFocusChanged(paramBoolean);
    }
    
    public void surfaceChanged(SurfaceHolder paramSurfaceHolder, int paramInt1, int paramInt2, int paramInt3)
    {
      PApplet.this.surfaceChanged = true;
    }
    
    public void surfaceCreated(SurfaceHolder paramSurfaceHolder) {}
    
    public void surfaceDestroyed(SurfaceHolder paramSurfaceHolder) {}
  }
  
  public class SketchSurfaceViewGL
    extends GLSurfaceView
  {
    PGraphicsOpenGL g3;
    SurfaceHolder surfaceHolder;
    
    public SketchSurfaceViewGL(Context paramContext, int paramInt1, int paramInt2, boolean paramBoolean)
    {
      super();
      if (((ActivityManager)PApplet.this.getSystemService("activity")).getDeviceConfigurationInfo().reqGlEsVersion >= 131072) {}
      for (int i = 1; i == 0; i = 0) {
        throw new RuntimeException("OpenGL ES 2.0 is not supported by this device.");
      }
      this.surfaceHolder = getHolder();
      this.surfaceHolder.addCallback(this);
      if (paramBoolean) {}
      for (this.g3 = new PGraphics3D();; this.g3 = new PGraphics2D())
      {
        this.g3.setParent(PApplet.this);
        this.g3.setPrimary(true);
        this.g3.setSize(paramInt1, paramInt2);
        setEGLContextClientVersion(2);
        setRenderer(((PGLES)this.g3.pgl).getRenderer());
        setRenderMode(0);
        PApplet.this.g = this.g3;
        setFocusable(true);
        setFocusableInTouchMode(true);
        requestFocus();
        return;
      }
    }
    
    public PGraphics getGraphics()
    {
      return this.g3;
    }
    
    public boolean onKeyDown(int paramInt, android.view.KeyEvent paramKeyEvent)
    {
      return PApplet.this.surfaceKeyDown(paramInt, paramKeyEvent);
    }
    
    public boolean onKeyUp(int paramInt, android.view.KeyEvent paramKeyEvent)
    {
      return PApplet.this.surfaceKeyUp(paramInt, paramKeyEvent);
    }
    
    public boolean onTouchEvent(MotionEvent paramMotionEvent)
    {
      return PApplet.this.surfaceTouchEvent(paramMotionEvent);
    }
    
    public void onWindowFocusChanged(boolean paramBoolean)
    {
      PApplet.this.surfaceWindowFocusChanged(paramBoolean);
    }
    
    public void surfaceChanged(SurfaceHolder paramSurfaceHolder, int paramInt1, int paramInt2, int paramInt3)
    {
      super.surfaceChanged(paramSurfaceHolder, paramInt1, paramInt2, paramInt3);
      PApplet.this.surfaceChanged = true;
    }
    
    public void surfaceCreated(SurfaceHolder paramSurfaceHolder)
    {
      super.surfaceCreated(paramSurfaceHolder);
    }
    
    public void surfaceDestroyed(SurfaceHolder paramSurfaceHolder)
    {
      super.surfaceDestroyed(paramSurfaceHolder);
    }
  }
}
