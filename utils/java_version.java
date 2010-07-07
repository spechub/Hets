/*
 * Determine your JDK
 */

import java.lang.management.RuntimeMXBean;
import java.lang.management.ManagementFactory;
import java.util.Map;

/**
 *
 * @author luecke
 */
public class java_version {

    /**
     * @param None
     */
    public static void main(String[] args) {
        RuntimeMXBean mxBean = ManagementFactory.getRuntimeMXBean();
        Map<String, String> p = mxBean.getSystemProperties();
        System.out.println("Vendor:   " + mxBean.getVmVendor());
        System.out.println("VM Name:  " + mxBean.getVmName() + " " + 
                mxBean.getVmVersion());
        System.out.println("Runtime:  " + p.get("java.runtime.name") + " " +
                p.get("java.runtime.version"));
    }

}
