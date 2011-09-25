package cvc3;

import java.util.*;
import java.lang.reflect.Constructor;

public class JniUtils {

    // check that list is an instance of a class -
    // generics would avoid that
    public static boolean listInstanceof(List list, Class c) {
	Iterator i = list.iterator();
	while (i.hasNext()) {
	    if (!(c.isInstance(i.next()))) return false;
	}
	return true;
    }

    public static boolean listListInstanceof(List listList, Class c) {
	Iterator i = listList.iterator();
	while (i.hasNext()) {
	    Object list = i.next();
	    assert(list instanceof List);
	    if (!(listInstanceof((List)list, c))) return false;
	}
	return true;
    }

    public static boolean listListListInstanceof(List listListList, Class c) {
	Iterator i = listListList.iterator();
	while (i.hasNext()) {
	    Object list = i.next();
	    assert(list instanceof List);
	    if (!(listListInstanceof((List)list, c))) return false;
	}
	return true;
    }


    // embed an array of c++ objects in a list
    public static List embedList(Object[] cobjects, Class c, EmbeddedManager embeddedManager) {
	List embedded = new ArrayList();

	try {
	    Class[] argsC = new Class[2];
	    argsC[0] = Object.class;
	    argsC[1] = EmbeddedManager.class;
	    Constructor constr = c.getConstructor(argsC);
	    
	    Object[] args = new Object[2];
	    for (int i = 0; i < cobjects.length; ++i) {
		args[0] = cobjects[i];
		args[1] = embeddedManager;
		embedded.add(constr.newInstance(args));
	    }
	} catch (NoSuchMethodException e) {
	    System.out.println(e);
	    assert(false);
	} catch (InstantiationException e) {
	    System.out.println(e);
	    assert(false);
	} catch (IllegalAccessException e) {
	    System.out.println(e);
	    assert(false);
	} catch (java.lang.reflect.InvocationTargetException e) {
	    System.out.println(e);
	    assert(false);
	}
	return embedded;
    }

    public static List embedListList(Object[][] cobjects, Class c, EmbeddedManager embeddedManager) {
      List embedded = new ArrayList(cobjects.length);
      for (int i = 0; i < cobjects.length; ++i) {
        Object[] cobject = cobjects[i];
        embedded.add( embedList(cobject,c,embeddedManager) );
      }
      return embedded;
    }
    
    // embed an array of c++ objects in a hash map
    public static HashMap embedHashMap(Object[] cobjects, Class ck, Class cv,
				       EmbeddedManager embeddedManager) {
	HashMap embedded = new HashMap(cobjects.length / 2);

	try {
	    Class[] argsCK = new Class[2];
	    argsCK[0] = Object.class;
	    argsCK[1] = EmbeddedManager.class;
	    Constructor constrK = ck.getConstructor(argsCK);
	    
	    Class[] argsCV = new Class[2];
	    argsCV[0] = Object.class;
	    argsCV[1] = EmbeddedManager.class;
	    Constructor constrV = cv.getConstructor(argsCV);

	    Object[] argsK = new Object[2];
	    Object[] argsV = new Object[2];
	    for (int i = 0; i < cobjects.length; ++i) {
		argsK[0] = cobjects[i];
		argsK[1] = embeddedManager;

		++i;
		assert(i < cobjects.length);
		argsV[0] = cobjects[i];
		argsV[1] = embeddedManager;
		
		embedded.put(constrK.newInstance(argsK), constrV.newInstance(argsV));
	    }
	} catch (NoSuchMethodException e) {
	    System.out.println(e);
	    assert(false);
	} catch (InstantiationException e) {
	    System.out.println(e);
	    assert(false);
	} catch (IllegalAccessException e) {
	    System.out.println(e);
	    assert(false);
	} catch (java.lang.reflect.InvocationTargetException e) {
	    System.out.println(e);
	    assert(false);
	}
	return embedded;
    }


    // unembed a list of Embedded objects to a list
    public static Object[] unembedList(List embedded) {
	Object[] unembedded = new Object[embedded.size()];

	for (int i = 0; i < embedded.size(); ++i) {
	    assert(embedded.get(i) instanceof Embedded);
	    unembedded[i] = ((Embedded)embedded.get(i)).embedded();
	}

	return unembedded;
    }

    public static Object[][] unembedListList(List embedded) {
	Object[][] unembedded = new Object[embedded.size()][];

	for (int i = 0; i < embedded.size(); ++i) {
	    Object list = embedded.get(i);
	    assert(list instanceof List);
	    unembedded[i] = unembedList((List)list);
	}

	return unembedded;
    }

    public static Object[][][] unembedListListList(List embedded) {
	Object[][][] unembedded = new Object[embedded.size()][][];

	for (int i = 0; i < embedded.size(); ++i) {
	    Object list = embedded.get(i);
	    assert(list instanceof List);
	    unembedded[i] = unembedListList((List)list);
	}

	return unembedded;
    }


    // unembed a list of Embedded objects to a list
    public static Object[] unembedArray(Object[] embedded) {
	Object[] unembedded = new Object[embedded.length];

	for (int i = 0; i < embedded.length; ++i) {
	    assert(embedded[i] instanceof Embedded);
	    unembedded[i] = ((Embedded)embedded[i]).embedded();
	}

	return unembedded;
    }

    public static Object[] unembedArrayArray(Object[][] embedded) {
	Object[] unembedded = new Object[embedded.length];

	for (int i = 0; i < embedded.length; ++i) {
	    unembedded[i] = unembedArray(embedded[i]);
	}

	return unembedded;
    }

    public static Object[] unembedArrayArrayArray(Object[][][] embedded) {
	Object[] unembedded = new Object[embedded.length];

	for (int i = 0; i < embedded.length; ++i) {
	    unembedded[i] = unembedArrayArray(embedded[i]);
	}

	return unembedded;
    }


    // copy a list of strings to a list
    public static Object[] toArray(List list) {
	assert(listInstanceof(list, String.class));
	assert(list.isEmpty() || !listInstanceof(list, Embedded.class));
	return list.toArray();
    }

    public static Object[] toArrayArray(List listList) {
	Object[] arrayArray = new Object[listList.size()];

	for (int i = 0; i < listList.size(); ++i) {
	    Object list = listList.get(i);
	    assert(list instanceof List);
	    arrayArray[i] = toArray(((List)list));
	}

	return arrayArray;
    }

    public static Object[] toArrayArrayArray(List listListList) {
	Object[] arrayArrayArray = new Object[listListList.size()];

	for (int i = 0; i < listListList.size(); ++i) {
	    Object list = listListList.get(i);
	    assert(list instanceof List);
	    arrayArrayArray[i] = toArrayArray((List)list);
	}

	return arrayArrayArray;
    }
}

